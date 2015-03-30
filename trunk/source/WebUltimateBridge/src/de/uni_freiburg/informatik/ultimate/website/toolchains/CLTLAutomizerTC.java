package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Setting.SettingType;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;


public class CLTLAutomizerTC extends WebToolchain {

	@Override
	protected String setDescription() {
		return "LTL Automizer toolchain";
	}

	@Override
	protected String setName() {
		return "LTL Automizer";
	}

	@Override
	protected String setId() {
		return "cLTLAutomizer";
	}

	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.LTLAUTOMIZER_C };
	}

    @Override
    protected String setLanguage() {
        return "c";
    }

    @Override
    protected String setUserInfo() {
        return "This webinterface is currently under construction and does not work!";
    }

	@Override
	protected List<Tool> setTools() {
		List<Tool> tools = new ArrayList<Tool>();
		
		// add CACSL2Boogie 
		List<Setting> optionalCACSLSettings = new ArrayList<Setting>();
		optionalCACSLSettings.add(new Setting(PrefStrings.s_CACSL_LABEL_StartFunction, SettingType.STRING,
				"Starting procedure: ", "main", true));
		
		tools.add(new Tool(PrefStrings.s_cacsl2boogietranslator, optionalCACSLSettings, new ArrayList<Setting>(),
				LoggingLevel.WARN));

		// add BoogiePreprocessor 
		tools.add(new Tool(PrefStrings.s_boogiePreprocessor));
		
		// add RCFGBuilder 
		List<Setting> oRCFGB = new ArrayList<Setting>();
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_Solver, PrefStrings.s_RCFG_LABEL_Solver,
        		new String[] { PrefStrings.s_RCFG_VALUE_SMTInterpol }, false, new String[] {
        		PrefStrings.s_RCFG_VALUE_SMTInterpol, PrefStrings.s_RCFG_VALUE_ExternalDefMo }, false));
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_BlockSize, PrefStrings.s_RCFG_LABEL_BlockSize,
        		new String[] { PrefStrings.s_RCFG_VALUE_Seq }, false, new String[] {
        		PrefStrings.s_RCFG_VALUE_Single, PrefStrings.s_RCFG_VALUE_Seq, PrefStrings.s_RCFG_VALUE_Block }, false));
		tools.add(new Tool(PrefStrings.s_rcfgBuilder, oRCFGB, new ArrayList<Setting>(), LoggingLevel.WARN));
		
		// add trace abstraction (checking safety first) 
        List<Setting> mTrAbs = new ArrayList<Setting>();
        mTrAbs.add(new Setting(PrefStrings.s_TA_LABEL_Interpol, Setting.SettingType.STRING,
                "interpolation", PrefStrings.s_TA_VALUE_CraigTree, false));
        mTrAbs.add(new Setting(PrefStrings.s_TA_LABEL_Hoare, Setting.SettingType.BOOLEAN,
                "Compute Hoare Annotation", "true", true));
        tools.add(new Tool(PrefStrings.s_traceAbstraction,  new ArrayList<Setting>(), mTrAbs,
                LoggingLevel.WARN));
		
		// add LTL2Aut
        tools.add(new Tool(PrefStrings.s_ltl2aut));
        
        // add buchiprogramproduct
        tools.add(new Tool(PrefStrings.s_buchiProgramProduct));
        
        // add buchi automizer
		List<Setting> oBA = new ArrayList<Setting>();
		oBA.add(new Setting(PrefStrings.s_TA_LABEL_Interpol, Setting.SettingType.STRING,
                "interpolation", PrefStrings.s_TA_VALUE_Forward, false));
		oBA.add(new Setting(PrefStrings.s_BA_LABEL_ExtSolverRank, Setting.SettingType.BOOLEAN,
				PrefStrings.s_BA_LABEL_ExtSolverRank, "false", false));
		oBA.add(new Setting(PrefStrings.s_BA_LABEL_Nonlinear, Setting.SettingType.BOOLEAN,
				"AllowNonlinearConstraints", "false", false));
		oBA.add(new Setting(PrefStrings.s_BA_LABEL_SimplifyTA, Setting.SettingType.BOOLEAN,
				PrefStrings.s_BA_LABEL_SimplifyTA, "true", false));
		tools.add(new Tool(PrefStrings.s_buchiautomizer, oBA, new ArrayList<Setting>(), LoggingLevel.WARN));
		
		
		return tools;
	}

	@Override
	protected LoggingLevel setPluginsLoggingLevel() {
		return LoggingLevel.INFO;
	}

	@Override
	protected LoggingLevel setToolsLoggingLevel() {
		return LoggingLevel.INFO;
	}
}
