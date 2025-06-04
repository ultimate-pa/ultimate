package de.uni_freiburg.informatik.ultimate.core.lib.util;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;

public final class ToolchainUtils {

	public static List<String> getPlugins(final IToolchain<RunDefinition> toolchain) {
		final IToolchainData<RunDefinition> toolchainData = toolchain.getCurrentToolchainData();
		final List<Object> initialChain = toolchainData.getRootElement().getToolchain().getPluginOrSubchain();
		return getPluginsRecursive(initialChain);
	}

	private static List<String> getPluginsRecursive(final List<Object> toolchainElements) {
		final List<String> toolchainPlugins = new ArrayList<>();

		for (final Object toolchainElement : toolchainElements) {
			if (toolchainElement instanceof final PluginType plugin) {
				toolchainPlugins.add(plugin.getId());
			} else if (toolchainElement instanceof final SubchainType subchain) {
				toolchainPlugins.addAll(getPluginsRecursive(subchain.getPluginOrSubchain()));
			}
		}

		return toolchainPlugins;
	}
}
