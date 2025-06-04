package de.uni_freiburg.informatik.ultimate.core.lib.results.convert;

/**
 * @author Manuel Bentele
 */
// public class ResultConverterOld<T> implements Function<Map<String, List<IResult>>, Output> {
//
// private final ICore<T> mCore;
//
// private final IToolchain<T> mToolchain;
//
// public ResultConverterOld(final ICore<T> core, final IToolchain<T> toolchain) {
// mCore = core;
// mToolchain = toolchain;
// }
//
// @Override
// public Output apply(final Map<String, List<IResult>> results) {
// return convert(results);
// }
//
// public String transform(final IResultWriter writer, final Map<String, List<IResult>> results) {
// return writer.formatResults(apply(results));
// }
//
// private Output convert(final Map<String, List<IResult>> results) {
//
// final String version = mCore.getUltimateVersionString();
//
// mCore.getRegisteredUltimatePlugins();
//
// // toolchain plugins, settings
//
// @Override
// public final Map<String, List<Entry<String, Object>>> getAllPreferencesPerPlugin() {
// return Arrays.stream(getRegisteredUltimatePluginIDs()).collect(Collectors.toMap(pluginId -> pluginId,
// pluginId -> new ArrayList<>(new RcpPreferenceProvider(pluginId).getPreferences().entrySet())));
// }
//
// @Override
// public Map<String, List<Entry<String, Object>>> getDiffPreferencesPerPlugin() {
// return Arrays.stream(getRegisteredUltimatePluginIDs()).collect(Collectors.toMap(pluginId -> pluginId,
// pluginId -> new ArrayList<>(new RcpPreferenceProvider(pluginId).getDeltaPreferences().entrySet())));
// }
//
// // final Map<String, String> mp = UltimateCore.getInformationService().getAllPreferences().entrySet().stream()
// // .collect(Collectors.toMap(Map.Entry::getKey, e -> e.getValue().toString()));
// final Map<String, List<Entry<String, Object>>> mp = mCore.getDiffPreferencesPerPlugin().entrySet().stream()
// .filter(e -> !e.getValue().isEmpty()).collect(Collectors.toMap(Entry::getKey, Entry::getValue));
//
// final Config config = new Config(Arrays.asList(UltimateCore.getPluginNames()), mp);
// // input files
// final Input input = new Input(new ArrayList<>());
// final Results resData = convertRes(results);
//
// final Date time = Date.from(Instant.now());
// final Content content = new Content(version, config, input, resData);
//
// return new Output(time, content);
// }
//
// private Map<String, List<Entry<String, Object>>> getAllPreferencesPerPlugin() {
// return Arrays.stream(mCore.getRegisteredUltimatePluginIDs()).collect(Collectors.toMap(pluginId -> pluginId,
// pluginId -> new ArrayList<>(new RcpPreferenceProvider(pluginId).getPreferences().entrySet())));
// }
//
// private Map<String, List<Entry<String, Object>>> getDiffPreferencesPerPlugin() {
// return Arrays.stream(mCore.getRegisteredUltimatePluginIDs()).collect(Collectors.toMap(pluginId -> pluginId,
// pluginId -> new ArrayList<>(new RcpPreferenceProvider(pluginId).getDeltaPreferences().entrySet())));
// }
//
// private Map<String, String> getAllRegisteredPlugins() {
// return Arrays.asList(mCore.getRegisteredUltimatePlugins()).stream()
// .collect(Collectors.toMap(IUltimatePlugin::getPluginID, IUltimatePlugin::getPluginName));
// }
//
// private Map<String, String> getAllToolchainPlugins() {
// if (mToolchain.getCurrentToolchainData() instanceof final ToolchainData chain) {
// final List<Object> tools = chain.getRootElement().getToolchain().getPluginOrSubchain();
// for (final Object tool : tools) {
// if (tool instanceof final IPluginType t) {
//
// }
// }
// }
// final IToolchainData<RunDefinition> chain = mToolchain.getCurrentToolchainData();
// if (chain instanceof final IToolchainData<RunDefinition> c) {
// c.getRootElement().getToolchain().getPluginOrSubchain();
// }
// ((RunConfiguration) chain.getRootElement()).getToolchain().getPluginOrSubchain();
// }
//
// protected abstract String serialize(T dto);
//
// private Results convertRes(final Map<String, List<IResult>> results) {
//
// for (final Entry<String, List<IResult>> entry : results.entrySet()) {
// final List<IResult> toolResults = entry.getValue();
// for (final IResult result : toolResults) {
//
// final String resPlugin = result.getPlugin();
// final String resShortDesc = result.getShortDescription();
// final String resLongDesc = result.getLongDescription();
//
// if (result instanceof IFailedAnalysisResult) {
// final IFailedAnalysisResult res = IFailedAnalysisResult.class.cast(result);
// // do nothing
// }
//
// if (result instanceof IResultWithCheck) {
// final IResultWithCheck res = IResultWithCheck.class.cast(result);
// res.getCheckedSpecification();
// }
//
// if (result instanceof IResultWithFiniteTrace) {
// final IResultWithFiniteTrace<?, ?> res = IResultWithFiniteTrace.class.cast(result);
// res.getFailurePath();
// res.getProgramExecution();
// }
//
// if (result instanceof IResultWithInfiniteLassoTrace) {
// final IResultWithInfiniteLassoTrace<?, ?> res = IResultWithInfiniteLassoTrace.class.cast(result);
// res.getLasso();
// res.getStem();
// }
//
// if (result instanceof IResultWithLocation) {
// final IResultWithLocation res = IResultWithLocation.class.cast(result);
// final ILocation loc = res.getLocation();
// loc.getAnnotationsAsMap();
// loc.getFileName();
// loc.getFunction();
// loc.getStartLine();
// loc.getEndLine();
// loc.getStartColumn();
// loc.getEndColumn();
// }
//
// if (result instanceof IResultWithSeverity) {
// final IResultWithSeverity res = IResultWithSeverity.class.cast(result);
// res.getSeverity();
// }
//
// if (result instanceof ITimeoutResult) {
// final ITimeoutResult res = ITimeoutResult.class.cast(result);
// // do nothing
// }
//
// // Do not handle classes here, only use methods defined by interfaces
// if (result instanceof StatisticsResult) {
// final StatisticsResult<?> res = StatisticsResult.class.cast(result);
// res.getStatistics();
// }
// }
// }
//
// return null;
// }
// }
