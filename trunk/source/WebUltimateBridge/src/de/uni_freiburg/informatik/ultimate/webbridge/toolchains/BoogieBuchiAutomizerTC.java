package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;


public class BoogieBuchiAutomizerTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_AUTOMIZER_BUCHI;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_AUTOMIZER_BUCHI;
	}

	@Override
	protected String defineId() {
		return "boogieBuchiAutomizer";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.TERMINATION_BOOGIE };
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
		return boogieBuchiAutomizerToolchain();
	}
	
	@Override
	protected List<Setting> defineAdditionalSettings() {
		return boogieBuchiAutomizerAdditionalSettings();
	}
	
	static List<Tool> boogieBuchiAutomizerToolchain() {
		final List<Tool> tools = new ArrayList<Tool>();
		
		tools.add(new Tool(PrefStrings.BOOGIE_PREPROCESSOR));
		tools.add(new Tool(PrefStrings.RCFGBUILDER));
//		TODO 2016-12-21 Matthias: Enable Blockencoding again after the 
//		backtranslation works.
//		tools.add(new Tool(PrefStrings.s_blockencoding));
		tools.add(new Tool(PrefStrings.BUCHIAUTOMIZER));
		
		return tools;
	}
	
	static List<Setting> boogieBuchiAutomizerAdditionalSettings() {
		final List<Setting> rtr = new ArrayList<>();
//		rtr.add(new Setting(PrefStrings.s_BE_LABEL_STRATEGY, PrefStrings.s_BE_LABEL_STRATEGY,
//        		new String[] { PrefStrings.s_BE_VALUE_DisjunctiveRating }, false, new String[] {
//				PrefStrings.s_BE_VALUE_DisjunctiveRating, PrefStrings.s_BE_VALUE_LargeBlock }, true));
		return rtr;
	}
	
	@Override
	protected String defineToolchainSettingsFile() {
		return "BuchiAutomizer.epf";
	}
}
