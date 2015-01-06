﻿//------------------------------------------------------------------------------
// <auto-generated>
//     This code was generated by a tool.
//     Runtime Version:4.0.30319.0
//
//     Changes to this file may cause incorrect behavior and will be lost if
//     the code is regenerated.
// </auto-generated>
//------------------------------------------------------------------------------

namespace Roslyn.Diagnostics.Analyzers {
    using System;
    
    
    /// <summary>
    ///   A strongly-typed resource class, for looking up localized strings, etc.
    /// </summary>
    // This class was auto-generated by the StronglyTypedResourceBuilder
    // class via a tool like ResGen or Visual Studio.
    // To add or remove a member, edit your .ResX file then rerun ResGen
    // with the /str option, or rebuild your VS project.
    [global::System.CodeDom.Compiler.GeneratedCodeAttribute("System.Resources.Tools.StronglyTypedResourceBuilder", "4.0.0.0")]
    [global::System.Diagnostics.DebuggerNonUserCodeAttribute()]
    [global::System.Runtime.CompilerServices.CompilerGeneratedAttribute()]
    internal class RoslynDiagnosticsResources {
        
        private static global::System.Resources.ResourceManager resourceMan;
        
        private static global::System.Globalization.CultureInfo resourceCulture;
        
        [global::System.Diagnostics.CodeAnalysis.SuppressMessageAttribute("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode")]
        internal RoslynDiagnosticsResources() {
        }
        
        /// <summary>
        ///   Returns the cached ResourceManager instance used by this class.
        /// </summary>
        [global::System.ComponentModel.EditorBrowsableAttribute(global::System.ComponentModel.EditorBrowsableState.Advanced)]
        internal static global::System.Resources.ResourceManager ResourceManager {
            get {
                if (object.ReferenceEquals(resourceMan, null)) {
                    global::System.Resources.ResourceManager temp = new global::System.Resources.ResourceManager("Roslyn.Diagnostics.Analyzers.RoslynDiagnosticsResources", typeof(RoslynDiagnosticsResources).Assembly);
                    resourceMan = temp;
                }
                return resourceMan;
            }
        }
        
        /// <summary>
        ///   Overrides the current thread's CurrentUICulture property for all
        ///   resource lookups using this strongly typed resource class.
        /// </summary>
        [global::System.ComponentModel.EditorBrowsableAttribute(global::System.ComponentModel.EditorBrowsableState.Advanced)]
        internal static global::System.Globalization.CultureInfo Culture {
            get {
                return resourceCulture;
            }
            set {
                resourceCulture = value;
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Given diagnostic analyzer seems to be marked with a DiagnosticAnalyzerAttribute with a specific supported language. However, the analyzer assembly doesn&apos;t seem to reference any language specific CodeAnalysis assemblies. Hence, it is likely a language-agnostic diagnostic analyzer. Consider either removing the argument to DiagnosticAnalyzerAttribute or adding a new DiagnosticAnalyzerAttribute for missing language..
        /// </summary>
        internal static string AddLanguageSupportToAnalyzerDescription {
            get {
                return ResourceManager.GetString("AddLanguageSupportToAnalyzerDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to &apos;{0}&apos; seems to be a language-agnostic diagnostic analyzer. Consider either removing the argument to DiagnosticAnalyzerAttribute or adding a new DiagnosticAnalyzerAttribute for &apos;{1}&apos; language support..
        /// </summary>
        internal static string AddLanguageSupportToAnalyzerMessage {
            get {
                return ResourceManager.GetString("AddLanguageSupportToAnalyzerMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Recommend adding language support to diagnostic analyzer..
        /// </summary>
        internal static string AddLanguageSupportToAnalyzerTitle {
            get {
                return ResourceManager.GetString("AddLanguageSupportToAnalyzerTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Apply language-agnostic DiagnosticAnalyzer attribute..
        /// </summary>
        internal static string ApplyDiagnosticAnalyzerAttribute_1 {
            get {
                return ResourceManager.GetString("ApplyDiagnosticAnalyzerAttribute_1", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Apply &apos;{0}&apos; DiagnosticAnalyzer attribute..
        /// </summary>
        internal static string ApplyDiagnosticAnalyzerAttribute_2 {
            get {
                return ResourceManager.GetString("ApplyDiagnosticAnalyzerAttribute_2", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Apply DiagnosticAnalyzer attributes for both: &apos;{0}&apos; and &apos;{1}&apos;..
        /// </summary>
        internal static string ApplyDiagnosticAnalyzerAttribute_3 {
            get {
                return ResourceManager.GetString("ApplyDiagnosticAnalyzerAttribute_3", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to CancellationToken parameters must come last.
        /// </summary>
        internal static string CancellationTokenMustBeLastDescription {
            get {
                return ResourceManager.GetString("CancellationTokenMustBeLastDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Method &apos;{0}&apos; should take CancellationToken as the last parameter.
        /// </summary>
        internal static string CancellationTokenMustBeLastMessage {
            get {
                return ResourceManager.GetString("CancellationTokenMustBeLastMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to PreserveSigAttribute indicates that a method will return an HRESULT, rather than throwing an exception.  Therefore, it is important to consume the HRESULT returned by the method, so that errors can be detected.  Generally, this is done by calling Marshal.ThrowExceptionForHR..
        /// </summary>
        internal static string ConsumePreserveSigDescription {
            get {
                return ResourceManager.GetString("ConsumePreserveSigDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Consume the hresult returned by method &apos;{0}&apos; and call Marshal.ThrowExceptionForHR..
        /// </summary>
        internal static string ConsumePreserveSigMessage {
            get {
                return ResourceManager.GetString("ConsumePreserveSigMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Always consume the value returned by methods marked with PreserveSigAttribute.
        /// </summary>
        internal static string ConsumePreserveSigTitle {
            get {
                return ResourceManager.GetString("ConsumePreserveSigTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Accessing the Descriptor property of Diagnostic in compiler layer leads to unnecessary string allocations for fields of the descriptor that are not utilized in command line compilation. Hence, you should avoid accessing the Descriptor of the compiler diagnostics here. Instead you should directly access these properties off the Diagnostic type..
        /// </summary>
        internal static string DiagnosticDescriptorAccessDescription {
            get {
                return ResourceManager.GetString("DiagnosticDescriptorAccessDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not invoke property &apos;{0}&apos; on type &apos;{1}&apos;, instead directly access the required member{2} on &apos;{1}&apos;.
        /// </summary>
        internal static string DiagnosticDescriptorAccessMessage {
            get {
                return ResourceManager.GetString("DiagnosticDescriptorAccessMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not invoke Diagnostic.Descriptor.
        /// </summary>
        internal static string DiagnosticDescriptorAccessTitle {
            get {
                return ResourceManager.GetString("DiagnosticDescriptorAccessTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not directly await a Task.
        /// </summary>
        internal static string DirectlyAwaitingTaskDescription {
            get {
                return ResourceManager.GetString("DirectlyAwaitingTaskDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not directly await a Task without calling ConfigureAwait.
        /// </summary>
        internal static string DirectlyAwaitingTaskMessage {
            get {
                return ResourceManager.GetString("DirectlyAwaitingTaskMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not call ToImmutableArray on an ImmutableArray&lt;T&gt; value..
        /// </summary>
        internal static string DoNotCallToImmutableArrayMessage {
            get {
                return ResourceManager.GetString("DoNotCallToImmutableArrayMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to This collection is directly indexable.  Going through LINQ here causes unnecessary allocations and CPU work..
        /// </summary>
        internal static string DoNotUseLinqOnIndexableCollectionDescription {
            get {
                return ResourceManager.GetString("DoNotUseLinqOnIndexableCollectionDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not use Enumerable methods on indexable collections.  Instead use the collection directly..
        /// </summary>
        internal static string DoNotUseLinqOnIndexableCollectionMessage {
            get {
                return ResourceManager.GetString("DoNotUseLinqOnIndexableCollectionMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not use generic CodeAction.Create to create CodeAction.
        /// </summary>
        internal static string DontUseCodeActionCreateDescription {
            get {
                return ResourceManager.GetString("DontUseCodeActionCreateDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Consider creating unique code action type per different fix. it will help us to see how each code action is used. otherwise, we will only see bunch of generic code actions being used..
        /// </summary>
        internal static string DontUseCodeActionCreateMessage {
            get {
                return ResourceManager.GetString("DontUseCodeActionCreateMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Implement IEquatable&lt;T&gt; when overriding Object.Equals.
        /// </summary>
        internal static string ImplementIEquatableDescription {
            get {
                return ResourceManager.GetString("ImplementIEquatableDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Type {0} should implement IEquatable&lt;T&gt; because it overrides Equals.
        /// </summary>
        internal static string ImplementIEquatableMessage {
            get {
                return ResourceManager.GetString("ImplementIEquatableMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to ReportDiagnostic should only be invoked with supported DiagnosticDescriptors that are returned from DiagnosticAnalyzer.SupportedDiagnostics property. Otherwise, the reported diagnostic will be filtered out by the analysis engine..
        /// </summary>
        internal static string InvalidReportDiagnosticDescription {
            get {
                return ResourceManager.GetString("InvalidReportDiagnosticDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to ReportDiagnostic invoked with an unsupported DiagnosticDescriptor &apos;{0}&apos;..
        /// </summary>
        internal static string InvalidReportDiagnosticMessage {
            get {
                return ResourceManager.GetString("InvalidReportDiagnosticMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to ReportDiagnostic invoked with an unsupported DiagnosticDescriptor..
        /// </summary>
        internal static string InvalidReportDiagnosticTitle {
            get {
                return ResourceManager.GetString("InvalidReportDiagnosticTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Missing &apos;{0}&apos; attribute..
        /// </summary>
        internal static string MissingAttributeMessage {
            get {
                return ResourceManager.GetString("MissingAttributeMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Non-abstract sub-types of DiagnosticAnalyzer should be marked with DiagnosticAnalyzerAttribute(s). The argument to this attribute(s), if any, determine the supported languages for the analyzer. Analyzer types without this attribute will be ignored by the analysis engine..
        /// </summary>
        internal static string MissingDiagnosticAnalyzerAttributeDescription {
            get {
                return ResourceManager.GetString("MissingDiagnosticAnalyzerAttributeDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Missing diagnostic analyzer attribute..
        /// </summary>
        internal static string MissingDiagnosticAnalyzerAttributeTitle {
            get {
                return ResourceManager.GetString("MissingDiagnosticAnalyzerAttributeTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to You must specify at least one syntax/symbol kinds of interest while registering a syntax/symbol analyzer action. Otherwise, the registered action will be dead code and will never be invoked during analysis..
        /// </summary>
        internal static string MissingKindArgumentToRegisterActionDescription {
            get {
                return ResourceManager.GetString("MissingKindArgumentToRegisterActionDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Specify at least one &apos;{0}&apos; of interest while registering a {1} analyzer action..
        /// </summary>
        internal static string MissingKindArgumentToRegisterActionMessage {
            get {
                return ResourceManager.GetString("MissingKindArgumentToRegisterActionMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Missing kind argument while registering an analyzer action..
        /// </summary>
        internal static string MissingKindArgumentToRegisterActionTitle {
            get {
                return ResourceManager.GetString("MissingKindArgumentToRegisterActionTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Parts exported with MEFv2 must be marked as Shared..
        /// </summary>
        internal static string MissingSharedAttributeDescription {
            get {
                return ResourceManager.GetString("MissingSharedAttributeDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Part exported with MEFv2 must be marked with the Shared attribute..
        /// </summary>
        internal static string MissingSharedAttributeMessage {
            get {
                return ResourceManager.GetString("MissingSharedAttributeMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not mix attributes from different versions of MEF.
        /// </summary>
        internal static string MixedVersionsOfMefAttributesDescription {
            get {
                return ResourceManager.GetString("MixedVersionsOfMefAttributesDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Attribute &apos;{0}&apos; comes from a different version of MEF than the export attribute on &apos;{1}&apos;.
        /// </summary>
        internal static string MixedVersionsOfMefAttributesMessage {
            get {
                return ResourceManager.GetString("MixedVersionsOfMefAttributesMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Override Object.Equals(object) when implementing IEquatable&lt;T&gt; .
        /// </summary>
        internal static string OverrideObjectEqualsDescription {
            get {
                return ResourceManager.GetString("OverrideObjectEqualsDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Type {0} should override Equals because it implements IEquatable&lt;T&gt;.
        /// </summary>
        internal static string OverrideObjectEqualsMessage {
            get {
                return ResourceManager.GetString("OverrideObjectEqualsMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to SymbolKind &apos;{0}&apos; is not supported for symbol analyzer actions..
        /// </summary>
        internal static string UnsupportedSymbolKindArgumentToRegisterActionMessage {
            get {
                return ResourceManager.GetString("UnsupportedSymbolKindArgumentToRegisterActionMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Unsupported SymbolKind argument while registering a symbol analyzer action..
        /// </summary>
        internal static string UnsupportedSymbolKindArgumentToRegisterActionTitle {
            get {
                return ResourceManager.GetString("UnsupportedSymbolKindArgumentToRegisterActionTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Avoid zero-length array allocations..
        /// </summary>
        internal static string UseArrayEmptyDescription {
            get {
                return ResourceManager.GetString("UseArrayEmptyDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Avoid unnecessary zero-length array allocations.  Use Array.Empty&lt;T&gt;() instead..
        /// </summary>
        internal static string UseArrayEmptyMessage {
            get {
                return ResourceManager.GetString("UseArrayEmptyMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Use SpecializedCollections.EmptyEnumerable&lt;T&gt;().
        /// </summary>
        internal static string UseEmptyEnumerableDescription {
            get {
                return ResourceManager.GetString("UseEmptyEnumerableDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Use SpecializedCollections.EmptyEnumerable&lt;T&gt;().
        /// </summary>
        internal static string UseEmptyEnumerableMessage {
            get {
                return ResourceManager.GetString("UseEmptyEnumerableMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Use of cref tags with prefixes should be avoided, since it prevents the compiler from verifying references and the IDE from updating references during refactorings. It is permissible to suppress this error at a single documentation site if the cref must use a prefix because the type being mentioned is not findable by the compiler. For example, if a cref is mentioning a special attribute in the full framework but you’re in a file that compiles against the portable framework, or if you want to reference a typ [rest of string was truncated]&quot;;.
        /// </summary>
        internal static string UseProperCrefTagsDescription {
            get {
                return ResourceManager.GetString("UseProperCrefTagsDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to cref tag has prefix &apos;{0}&apos;, which should be removed unless the type or member cannot be accessed..
        /// </summary>
        internal static string UseProperCrefTagsMessage {
            get {
                return ResourceManager.GetString("UseProperCrefTagsMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Avoid using cref tags with a prefix.
        /// </summary>
        internal static string UseProperCrefTagsTitle {
            get {
                return ResourceManager.GetString("UseProperCrefTagsTitle", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Use SpecializedCollections.SingletonEnumerable&lt;T&gt;().
        /// </summary>
        internal static string UseSingletonEnumerableDescription {
            get {
                return ResourceManager.GetString("UseSingletonEnumerableDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Use SpecializedCollections.SingletonEnumerable&lt;T&gt;().
        /// </summary>
        internal static string UseSingletonEnumerableMessage {
            get {
                return ResourceManager.GetString("UseSingletonEnumerableMessage", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Invoke the correct property to ensure correct use site diagnostics..
        /// </summary>
        internal static string UseSiteDiagnosticsCheckerDescription {
            get {
                return ResourceManager.GetString("UseSiteDiagnosticsCheckerDescription", resourceCulture);
            }
        }
        
        /// <summary>
        ///   Looks up a localized string similar to Do not directly invoke the property &apos;{0}&apos;, instead use &apos;{0}NoUseSiteDiagnostics&apos;..
        /// </summary>
        internal static string UseSiteDiagnosticsCheckerMessage {
            get {
                return ResourceManager.GetString("UseSiteDiagnosticsCheckerMessage", resourceCulture);
            }
        }
    }
}
