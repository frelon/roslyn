// Copyright (c) Microsoft.  All Rights Reserved.  Licensed under the Apache License, Version 2.0.  See License.txt in the project root for license information.

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis.CodeActions;
using Microsoft.CodeAnalysis.CodeRefactorings;
using Microsoft.CodeAnalysis.CSharp.CodeGeneration;
using Microsoft.CodeAnalysis.CSharp.Extensions;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Editing;
using Microsoft.CodeAnalysis.Formatting;
using Microsoft.CodeAnalysis.Shared.Extensions;
using Microsoft.CodeAnalysis.Simplification;
using Roslyn.Utilities;

namespace Microsoft.CodeAnalysis.CSharp.CodeRefactorings.InvertIf
{
    // [ExportCodeRefactoringProvider(LanguageNames.CSharp, Name = PredefinedCodeRefactoringProviderNames.InvertIf)]
    internal partial class InvertIfCodeRefactoringProvider : CodeRefactoringProvider
    {
        private static readonly Dictionary<SyntaxKind, (SyntaxKind, SyntaxKind)> s_binaryMap =
            new Dictionary<SyntaxKind, (SyntaxKind, SyntaxKind)>(SyntaxFacts.EqualityComparer)
                {
                    { SyntaxKind.EqualsExpression, (SyntaxKind.NotEqualsExpression, SyntaxKind.ExclamationEqualsToken) },
                    { SyntaxKind.NotEqualsExpression, (SyntaxKind.EqualsExpression, SyntaxKind.EqualsEqualsToken) },
                    { SyntaxKind.LessThanExpression, (SyntaxKind.GreaterThanOrEqualExpression, SyntaxKind.GreaterThanEqualsToken) },
                    { SyntaxKind.LessThanOrEqualExpression, (SyntaxKind.GreaterThanExpression, SyntaxKind.GreaterThanToken) },
                    { SyntaxKind.GreaterThanExpression, (SyntaxKind.LessThanOrEqualExpression, SyntaxKind.LessThanEqualsToken) },
                    { SyntaxKind.GreaterThanOrEqualExpression, (SyntaxKind.LessThanExpression, SyntaxKind.LessThanToken) },
                };

        public override async Task ComputeRefactoringsAsync(CodeRefactoringContext context)
        {
            var document = context.Document;
            var textSpan = context.Span;
            var cancellationToken = context.CancellationToken;

            if (!textSpan.IsEmpty)
            {
                return;
            }

            if (document.Project.Solution.Workspace.Kind == WorkspaceKind.MiscellaneousFiles)
            {
                return;
            }

            var root = await document.GetSyntaxRootAsync(cancellationToken).ConfigureAwait(false);
            var ifStatement = root.FindToken(textSpan.Start).GetAncestor<IfStatementSyntax>();
            if (ifStatement == null)
            {
                return;
            }

            if (!ifStatement.IfKeyword.Span.IntersectsWith(textSpan.Start))
            {
                return;
            }

            if (ifStatement.OverlapsHiddenPosition(cancellationToken))
            {
                return;
            }

            var invertIfStyle = await GetInvertIfStyleAsync().ConfigureAwait(false);
            if (invertIfStyle == InvertIfStyle.None)
            {
                return;
            }

            context.RegisterRefactoring(
                new MyCodeAction(
                    CSharpFeaturesResources.Invert_if_statement,
                    c => InvertIfAsync(document, ifStatement, invertIfStyle, c)));

            async Task<InvertIfStyle> GetInvertIfStyleAsync()
            {
                if (ifStatement.Else != null)
                {
                    return InvertIfStyle.Normal;
                }

                if (!ifStatement.Parent.IsKind(SyntaxKind.Block, out BlockSyntax parentBlock))
                {
                    return InvertIfStyle.None;
                }

                var semanticModel = await document.GetSemanticModelAsync(cancellationToken).ConfigureAwait(false);
                var ifControlFlow = semanticModel.AnalyzeControlFlow(ifStatement.Statement);
                var ifHasUnreachableEnd = !ifControlFlow.EndPointIsReachable;
                var followingControlFlow = semanticModel.AnalyzeControlFlow(ifStatement, parentBlock.Statements.Last());
                var followingHasUnreachableEnd = !followingControlFlow.EndPointIsReachable;

                if (ifHasUnreachableEnd && followingHasUnreachableEnd)
                {
                    return InvertIfStyle.ReplaceSubsequentStatements;
                }

                var result = GetInvertIfStyleFromContext();

                //if (ifHasUnreachableEnd)
                //{
                //    var exitPoints = ifControlFlow.ExitPoints;
                //    if (exitPoints.Length != 1 || exitPoints[0].RawKind != (int)result)
                //    {
                //        return InvertIfStyle.None;
                //    }
                //}

                return result;
                InvertIfStyle GetInvertIfStyleFromContext()
                {
                    StatementSyntax current = ifStatement;
                    foreach (var node in ifStatement.Ancestors())
                    {
                        switch (node.Kind())
                        {
                            case SyntaxKind.Block:
                                var block = (BlockSyntax)node;
                                if (ifHasUnreachableEnd || current == block.Statements.Last())
                                {
                                    current = block;
                                    continue;
                                }

                                return InvertIfStyle.None;
                            case SyntaxKind.SwitchSection:
                                return ifHasUnreachableEnd
                                    ? InvertIfStyle.MoveSubsequentStatements
                                    : InvertIfStyle.WithBreakStatement;
                            case SyntaxKind.LocalFunctionStatement:
                                return ifHasUnreachableEnd
                                    ? InvertIfStyle.MoveSubsequentStatements
                                    : InvertIfStyle.WithReturnStatement;
                            case SyntaxKind.DoStatement:
                            case SyntaxKind.WhileStatement:
                            case SyntaxKind.ForStatement:
                            case SyntaxKind.ForEachStatement:
                            case SyntaxKind.ForEachVariableStatement:
                                return ifHasUnreachableEnd
                                    ? InvertIfStyle.MoveSubsequentStatements
                                    : InvertIfStyle.WithContinueStatement;
                        }

                        if (node is AccessorDeclarationSyntax ||
                            node is BaseMethodDeclarationSyntax ||
                            node is AnonymousFunctionExpressionSyntax)
                        {
                            return ifHasUnreachableEnd
                                ? InvertIfStyle.MoveSubsequentStatements
                                : InvertIfStyle.WithReturnStatement;
                        }
                    }

                        return InvertIfStyle.None;
                    }
            }
        }

        private async Task<Document> InvertIfAsync(Document document, IfStatementSyntax ifNode, InvertIfStyle invertIfStyle, CancellationToken cancellationToken)
        {
            var tree = await document.GetSyntaxTreeAsync(cancellationToken).ConfigureAwait(false);
            var root = await tree.GetRootAsync(cancellationToken).ConfigureAwait(false);

            var semanticModel = await document.GetSemanticModelAsync(cancellationToken).ConfigureAwait(false);
            var negatedCondition = Negate(ifNode.Condition, semanticModel, cancellationToken);

            switch (invertIfStyle)
            {
                case InvertIfStyle.Normal:
                    {
                        // In the case that the else clause is actually an else if clause, place the if
                        // statement to be moved in a new block in order to make sure that the else
                        // statement matches the right if statement after the edit.
                        var newIfNodeStatement = ifNode.Else.Statement.Kind() == SyntaxKind.IfStatement ?
                            SyntaxFactory.Block(ifNode.Else.Statement) :
                            ifNode.Else.Statement;

                        var invertedIf = ifNode.WithCondition(negatedCondition)
                                    .WithStatement(newIfNodeStatement)
                                    .WithElse(ifNode.Else.WithStatement(ifNode.Statement))
                                    .WithAdditionalAnnotations(Formatter.Annotation);

                        var result = root.ReplaceNode(ifNode, invertedIf);
                        return document.WithSyntaxRoot(result);
                    }

                case InvertIfStyle.ReplaceSubsequentStatements:
                    {
                        var ifBody = ifNode.Statement;

                        var currentParent = ifNode.Parent;
                        var statements = GetStatements(currentParent);
                        var index = statements.IndexOf(ifNode);

                        var statementsBeforeIf = statements.Take(index);
                        var statementsAfterIf = statements.Skip(index + 1).ToArray();

                        var updatedIf = ifNode
                            .WithCondition(negatedCondition)
                            .WithStatement(ReplaceEmbeddedStatement(ifNode.Statement, statementsAfterIf));

                        var updatedParent = SyntaxFactory.Block(statementsBeforeIf.Concat(updatedIf).Concat(UnwrapBlock(ifBody)))
                            .WithAdditionalAnnotations(Formatter.Annotation);

                        return document.WithSyntaxRoot(root.ReplaceNode(currentParent, updatedParent));
                    }

                case InvertIfStyle.WithReturnStatement:
                case InvertIfStyle.WithContinueStatement:
                case InvertIfStyle.WithBreakStatement:
                    {
                        var newIfBody = GetIfStatementBody();
                        var updatedIf = ifNode.WithCondition(negatedCondition)
                            .WithStatement(SyntaxFactory.Block(newIfBody));

                        var currentParent = ifNode.Parent;
                        var statements = GetStatements(currentParent);
                        var index = statements.IndexOf(ifNode);

                        var statementsBeforeIf = statements.Take(index);

                        var updatedParent = SyntaxFactory.Block(statementsBeforeIf.Concat(updatedIf).Concat(UnwrapBlock(ifNode.Statement)))
                            .WithAdditionalAnnotations(Formatter.Annotation);

                        return document.WithSyntaxRoot(root.ReplaceNode(currentParent, updatedParent));

                        StatementSyntax GetIfStatementBody()
                        {
                            switch (invertIfStyle)
                            {
                                case InvertIfStyle.WithContinueStatement:
                                    return SyntaxFactory.ContinueStatement();
                                case InvertIfStyle.WithReturnStatement:
                                    return SyntaxFactory.ReturnStatement();
                                case InvertIfStyle.WithBreakStatement:
                                    return SyntaxFactory.BreakStatement();
                                default:
                                    throw ExceptionUtilities.UnexpectedValue(invertIfStyle);
                            }
                        }
                    }

                case InvertIfStyle.MoveSubsequentStatements:
                    {
                        var currentParent = ifNode.Parent;
                        var statements = GetStatements(currentParent);
                        var index = statements.IndexOf(ifNode);

                        var statementsBeforeIf = statements.Take(index);
                        var statementsAfterIf = statements.Skip(index + 1).ToArray();

                        var updatedIf = ifNode
                             .WithCondition(negatedCondition)
                             .WithStatement(ReplaceEmbeddedStatement(ifNode.Statement, statementsAfterIf));

                        var updatedParent = SyntaxFactory.Block(statementsBeforeIf.Concat(updatedIf))
                            .WithAdditionalAnnotations(Formatter.Annotation);

                        return document.WithSyntaxRoot(root.ReplaceNode(currentParent, updatedParent));
                    }

                case InvertIfStyle.WithElseClause:
                    throw new NotImplementedException();
                default:
                    throw ExceptionUtilities.UnexpectedValue(invertIfStyle);
            }
        }

        private static IEnumerable<StatementSyntax> UnwrapBlock(StatementSyntax ifBody)
        {
            return ifBody is BlockSyntax block ? block.Statements : (IEnumerable<StatementSyntax>)new[] { ifBody };
        }

        private static StatementSyntax ReplaceEmbeddedStatement(StatementSyntax statement, StatementSyntax[] statements)
        {
            return statement is BlockSyntax block
                ? block.WithStatements(SyntaxFactory.List(statements))
                : statements.Length == 1 ? statements[0] : SyntaxFactory.Block(statements);
        }

        private static SyntaxList<StatementSyntax> GetStatements(SyntaxNode node)
        {
            switch (node)
            {
                case BlockSyntax n:
                    return n.Statements;
                case SwitchSectionSyntax n:
                    return n.Statements;
                default:
                    throw ExceptionUtilities.UnexpectedValue(node.Kind());
            }
        }

        private bool IsComparisonOfZeroAndSomethingNeverLessThanZero(BinaryExpressionSyntax binaryExpression, SemanticModel semanticModel, CancellationToken cancellationToken)
        {
            var canSimplify = false;

            if (binaryExpression.Kind() == SyntaxKind.GreaterThanExpression &&
                binaryExpression.Right.Kind() == SyntaxKind.NumericLiteralExpression)
            {
                canSimplify = CanSimplifyToLengthEqualsZeroExpression(
                    binaryExpression.Left,
                    (LiteralExpressionSyntax)binaryExpression.Right,
                    semanticModel,
                    cancellationToken);
            }
            else if (binaryExpression.Kind() == SyntaxKind.LessThanExpression &&
                     binaryExpression.Left.Kind() == SyntaxKind.NumericLiteralExpression)
            {
                canSimplify = CanSimplifyToLengthEqualsZeroExpression(
                    binaryExpression.Right,
                    (LiteralExpressionSyntax)binaryExpression.Left,
                    semanticModel,
                    cancellationToken);
            }
            else if (binaryExpression.Kind() == SyntaxKind.EqualsExpression &&
                     binaryExpression.Right.Kind() == SyntaxKind.NumericLiteralExpression)
            {
                canSimplify = CanSimplifyToLengthEqualsZeroExpression(
                    binaryExpression.Left,
                    (LiteralExpressionSyntax)binaryExpression.Right,
                    semanticModel,
                    cancellationToken);
            }
            else if (binaryExpression.Kind() == SyntaxKind.EqualsExpression &&
                     binaryExpression.Left.Kind() == SyntaxKind.NumericLiteralExpression)
            {
                canSimplify = CanSimplifyToLengthEqualsZeroExpression(
                    binaryExpression.Right,
                    (LiteralExpressionSyntax)binaryExpression.Left,
                    semanticModel,
                    cancellationToken);
            }

            return canSimplify;
        }

        private bool CanSimplifyToLengthEqualsZeroExpression(
            ExpressionSyntax variableExpression,
            LiteralExpressionSyntax numericLiteralExpression,
            SemanticModel semanticModel,
            CancellationToken cancellationToken)
        {
            var numericValue = semanticModel.GetConstantValue(numericLiteralExpression, cancellationToken);
            if (numericValue.HasValue && numericValue.Value is int && (int)numericValue.Value == 0)
            {
                var symbol = semanticModel.GetSymbolInfo(variableExpression, cancellationToken).Symbol;

                if (symbol != null && (symbol.Name == "Length" || symbol.Name == "LongLength"))
                {
                    var containingType = symbol.ContainingType;
                    if (containingType != null &&
                        (containingType.SpecialType == SpecialType.System_Array ||
                         containingType.SpecialType == SpecialType.System_String))
                    {
                        return true;
                    }
                }

                var typeInfo = semanticModel.GetTypeInfo(variableExpression, cancellationToken);
                if (typeInfo.Type != null)
                {
                    switch (typeInfo.Type.SpecialType)
                    {
                        case SpecialType.System_Byte:
                        case SpecialType.System_UInt16:
                        case SpecialType.System_UInt32:
                        case SpecialType.System_UInt64:
                            return true;
                    }
                }
            }

            return false;
        }

        private bool TryNegateBinaryComparisonExpression(
            ExpressionSyntax expression,
            SemanticModel semanticModel,
            CancellationToken cancellationToken,
            out ExpressionSyntax result)
        {
            if (s_binaryMap.TryGetValue(expression.Kind(), out var tuple))
            {
                var binaryExpression = (BinaryExpressionSyntax)expression;
                var expressionType = tuple.Item1;
                var operatorType = tuple.Item2;

                // Special case negating Length > 0 to Length == 0 and 0 < Length to 0 == Length
                // for arrays and strings. We can do this because we know that Length cannot be
                // less than 0. Additionally, if we find Length == 0 or 0 == Length, we'll invert
                // it to Length > 0 or 0 < Length, respectively.
                if (IsComparisonOfZeroAndSomethingNeverLessThanZero(binaryExpression, semanticModel, cancellationToken))
                {
                    operatorType = binaryExpression.OperatorToken.Kind() == SyntaxKind.EqualsEqualsToken
                        ? binaryExpression.Right is LiteralExpressionSyntax ? SyntaxKind.GreaterThanToken : SyntaxKind.LessThanToken
                        : SyntaxKind.EqualsEqualsToken;
                    expressionType = binaryExpression.Kind() == SyntaxKind.EqualsExpression
                        ? binaryExpression.Right is LiteralExpressionSyntax ? SyntaxKind.GreaterThanExpression : SyntaxKind.LessThanExpression
                        : SyntaxKind.EqualsExpression;
                }

                result = SyntaxFactory.BinaryExpression(
                    expressionType,
                    binaryExpression.Left,
                    SyntaxFactory.Token(
                        binaryExpression.OperatorToken.LeadingTrivia,
                        operatorType,
                        binaryExpression.OperatorToken.TrailingTrivia),
                    binaryExpression.Right);

                return true;
            }

            result = null;
            return false;
        }

        private ExpressionSyntax Negate(ExpressionSyntax expression, SemanticModel semanticModel, CancellationToken cancellationToken)
        {
            if (TryNegateBinaryComparisonExpression(expression, semanticModel, cancellationToken, out var result))
            {
                return result;
            }

            switch (expression.Kind())
            {
                case SyntaxKind.ParenthesizedExpression:
                    {
                        var parenthesizedExpression = (ParenthesizedExpressionSyntax)expression;
                        return parenthesizedExpression
                            .WithExpression(Negate(parenthesizedExpression.Expression, semanticModel, cancellationToken))
                            .WithAdditionalAnnotations(Simplifier.Annotation);
                    }

                case SyntaxKind.LogicalNotExpression:
                    {
                        var logicalNotExpression = (PrefixUnaryExpressionSyntax)expression;

                        var notToken = logicalNotExpression.OperatorToken;
                        var nextToken = logicalNotExpression.Operand.GetFirstToken(
                            includeZeroWidth: true, includeSkipped: true, includeDirectives: true, includeDocumentationComments: true);

                        var existingTrivia = SyntaxFactory.TriviaList(
                            notToken.LeadingTrivia.Concat(
                                notToken.TrailingTrivia.Concat(
                                    nextToken.LeadingTrivia)));

                        var updatedNextToken = nextToken.WithLeadingTrivia(existingTrivia);

                        return logicalNotExpression.Operand.ReplaceToken(
                            nextToken,
                            updatedNextToken);
                    }

                case SyntaxKind.LogicalOrExpression:
                    {
                        var binaryExpression = (BinaryExpressionSyntax)expression;
                        result = SyntaxFactory.BinaryExpression(
                            SyntaxKind.LogicalAndExpression,
                            Negate(binaryExpression.Left, semanticModel, cancellationToken),
                            SyntaxFactory.Token(
                                binaryExpression.OperatorToken.LeadingTrivia,
                                SyntaxKind.AmpersandAmpersandToken,
                                binaryExpression.OperatorToken.TrailingTrivia),
                            Negate(binaryExpression.Right, semanticModel, cancellationToken));

                        return result
                            .Parenthesize()
                            .WithLeadingTrivia(binaryExpression.GetLeadingTrivia())
                            .WithTrailingTrivia(binaryExpression.GetTrailingTrivia());
                    }

                case SyntaxKind.LogicalAndExpression:
                    {
                        var binaryExpression = (BinaryExpressionSyntax)expression;
                        result = SyntaxFactory.BinaryExpression(
                            SyntaxKind.LogicalOrExpression,
                            Negate(binaryExpression.Left, semanticModel, cancellationToken),
                            SyntaxFactory.Token(
                                binaryExpression.OperatorToken.LeadingTrivia,
                                SyntaxKind.BarBarToken,
                                binaryExpression.OperatorToken.TrailingTrivia),
                            Negate(binaryExpression.Right, semanticModel, cancellationToken));

                        return result
                            .Parenthesize()
                            .WithLeadingTrivia(binaryExpression.GetLeadingTrivia())
                            .WithTrailingTrivia(binaryExpression.GetTrailingTrivia());
                    }

                case SyntaxKind.TrueLiteralExpression:
                    {
                        var literalExpression = (LiteralExpressionSyntax)expression;
                        return SyntaxFactory.LiteralExpression(
                            SyntaxKind.FalseLiteralExpression,
                            SyntaxFactory.Token(
                                literalExpression.Token.LeadingTrivia,
                                SyntaxKind.FalseKeyword,
                                literalExpression.Token.TrailingTrivia));
                    }

                case SyntaxKind.FalseLiteralExpression:
                    {
                        var literalExpression = (LiteralExpressionSyntax)expression;
                        return SyntaxFactory.LiteralExpression(
                            SyntaxKind.TrueLiteralExpression,
                            SyntaxFactory.Token(
                                literalExpression.Token.LeadingTrivia,
                                SyntaxKind.TrueKeyword,
                                literalExpression.Token.TrailingTrivia));
                    }
            }

            // Anything else we can just negate by adding a ! in front of the parenthesized expression.
            // Unnecessary parentheses will get removed by the simplification service.
            return SyntaxFactory.PrefixUnaryExpression(
                SyntaxKind.LogicalNotExpression,
                expression.Parenthesize());
        }

        private enum InvertIfStyle
        {
            None,
            // switch if and else
            Normal,
            // switch subsequent statements and if body
            ReplaceSubsequentStatements,
            // move subsequent statements to if body
            MoveSubsequentStatements,
            // invert and generete else
            WithElseClause,
            // invert and generate return
            WithReturnStatement = SyntaxKind.ReturnStatement,
            // invert and generate continue
            WithContinueStatement = SyntaxKind.ContinueStatement,
            // invert and generate break
            WithBreakStatement = SyntaxKind.BreakStatement,
        }

        private class MyCodeAction : CodeAction.DocumentChangeAction
        {
            public MyCodeAction(string title, Func<CancellationToken, Task<Document>> createChangedDocument) :
                base(title, createChangedDocument)
            {
            }
        }
    }
}

