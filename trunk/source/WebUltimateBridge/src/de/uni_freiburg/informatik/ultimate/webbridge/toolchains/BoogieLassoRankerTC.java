package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

public class BoogieLassoRankerTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_LASSO_RANKER;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_LASSO_RANKER;
	}

	@Override
	protected String defineId() {
		return "boogieLassoRanker";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.RANK_SYNTHESIS_BOOGIE };
	}

	@Override
	protected String defineLanguage() {
		return "boogie";
	}

	@Override
	protected String defineUserInfo() {
		return null;
	}
	
	@Override
	protected String defineInterfaceLayoutFontsize() {
		return PrefStrings.INTERFACE_LAYOUT_FONTSIZE_DEFAULT;
	}

	@Override
	protected String defineInterfaceLayoutOrientation() {
		return PrefStrings.INTERFACE_LAYOUT_ORIENTATION_DEFAULT;
	}

	@Override
	protected String defineInterfaceLayoutTransitions() {
		return PrefStrings.INTERFACE_LAYOUT_TRANSITION_DEFAULT;
	}

	@Override
	protected List<Tool> defineTools() {
		return boogieLassoRankerToolchain();
	}
	
	@Override
	protected List<Setting> defineAdditionalSettings() {
		return boogieLassoRankerAdditionalSettings();
	}

	/**
	 * List of tools required for LassoRanker on boogie code.
	 */
	static List<Tool> boogieLassoRankerToolchain() {
		final List<Tool> tools = new ArrayList<Tool>();

		tools.add(new Tool(PrefStrings.BOOGIE_PREPROCESSOR));
		tools.add(new Tool(PrefStrings.RCFGBUILDER));
		tools.add(new Tool(PrefStrings.BLOCKENCODING));
		tools.add(new Tool(PrefStrings.LASSO_RANKER));
		
		return tools;
	}

	static List<Setting> boogieLassoRankerAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();
//		rtr.add(new Setting(PrefStrings.s_BE_LABEL_STRATEGY, PrefStrings.s_BE_LABEL_STRATEGY,
//				new String[] { PrefStrings.s_BE_VALUE_DisjunctiveRating }, false, new String[] {
//						PrefStrings.s_BE_VALUE_DisjunctiveRating, PrefStrings.s_BE_VALUE_LargeBlock }, true));
		return rtr;
	}
	
	@Override
	protected String defineToolchainSettingsFile() {
		return "LassoRanker.epf";
	}
}
