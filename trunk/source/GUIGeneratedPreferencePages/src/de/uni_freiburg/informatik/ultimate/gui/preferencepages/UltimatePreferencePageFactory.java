package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;

import org.eclipse.jface.preference.IPreferenceNode;
import org.eclipse.jface.preference.PreferenceManager;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * 
 * Creates the automatically generated preference pages for Ultimate. Call
 * {@link #createPreferencePages()} e.g. after WorbenchWindow creation (in
 * {@link WorkbenchWindowAdvisor}.
 * 
 * @author dietsch
 * 
 */
public class UltimatePreferencePageFactory {

	private ICore mCore;

	public UltimatePreferencePageFactory(ICore core) {
		mCore = core;
	}

	public void createPreferencePages() {
		for (IUltimatePlugin plugin : mCore.getPlugins()) {
			if (plugin.getPreferences() != null) {
				UltimatePreferenceItem<?>[] preferenceItems = plugin.getPreferences().getDefaultPreferences();
				if (preferenceItems != null) {
					String parentNodeID = "GeneratedUltimatePreferences";

					if (plugin instanceof ITool) {
						parentNodeID = "ToolPlugins";
					}
					if (plugin instanceof IOutput) {
						parentNodeID = "OutputPlugins";
					}
					if (plugin instanceof ICore) {
						parentNodeID = "Core";
					}
					if (plugin instanceof ISource) {
						parentNodeID = "SourcePlugins";
					}

					createPreferencePage(plugin.getPluginID(), plugin.getPreferences().getPreferencePageTitle(),
							filterPreferences(preferenceItems), parentNodeID);
				}
			}
		}
	}

	private UltimatePreferenceItem<?>[] filterPreferences(UltimatePreferenceItem<?>[] items) {
		ArrayList<UltimatePreferenceItem<?>> list = new ArrayList<UltimatePreferenceItem<?>>();
		for (UltimatePreferenceItem<?> item : items) {
			if (!item.getUseCustomPreferencePage()) {
				list.add(item);
			}
		}
		return list.toArray(new UltimatePreferenceItem[list.size()]);
	}

	private void createPreferencePage(String pluginID, String title, UltimatePreferenceItem<?>[] preferenceItems,
			String parentNodeID) {
		UltimateGeneratedPreferencePage page = new UltimateGeneratedPreferencePage(pluginID, title, preferenceItems);

		UltimatePreferenceNode node = new UltimatePreferenceNode(pluginID, page);
		PreferenceManager pm = PlatformUI.getWorkbench().getPreferenceManager();

		IPreferenceNode root = findRootNode(pm, parentNodeID);
		if (root != null) {
			root.remove(pluginID);
			root.add(node);
			page.init(PlatformUI.getWorkbench());
		}
	}

	private IPreferenceNode findRootNode(PreferenceManager pm, String nodeID) {
		Queue<IPreferenceNode> toVisit = new LinkedList<IPreferenceNode>();
		for (IPreferenceNode node : pm.getRootSubNodes()) {
			toVisit.add(node);
		}

		while (!toVisit.isEmpty()) {
			IPreferenceNode current = toVisit.poll();
			if (current.getId().equals(nodeID)) {
				return current;
			}
			for (IPreferenceNode node : current.getSubNodes()) {
				toVisit.add(node);
			}
		}
		return null;
	}

}
