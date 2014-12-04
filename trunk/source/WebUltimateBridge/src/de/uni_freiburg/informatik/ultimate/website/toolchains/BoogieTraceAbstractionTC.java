/**
 * Boogie TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.WebToolchain;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public class BoogieTraceAbstractionTC extends WebToolchain {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setDescription()
	 */
	@Override
	protected String setDescription() {
		return "Trace abstraction toolchain";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setName()
	 */
	@Override
	protected String setName() {
		return "Trace Abstraction";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setId()
	 */
	@Override
	protected String setId() {
		return "boogieTraceAbstraction";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTaskName()
	 */
	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.VerifyBoogie };
	}

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.WebToolchain#setLanguage()
     */
    @Override
    protected String setLanguage() {
        return "boogie";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.WebToolchain#setUserInfo()
     */
    @Override
    protected String setUserInfo() {
        return null;
    }

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTools()
	 */
	@Override
	protected List<Tool> setTools() {
		List<Tool> tools = new ArrayList<Tool>();
		
		List<Setting> oPre = new ArrayList<Setting>();
		List<Setting> mPre = new ArrayList<Setting>();
		tools.add(new Tool(PrefStrings.s_boogiePreprocessor,
				oPre, mPre, LoggingLevel.WARN));
		
		List<Setting> oRCFGB = new ArrayList<Setting>();
		List<Setting> mRCFGB = new ArrayList<Setting>();
		tools.add(new Tool(PrefStrings.s_rcfgBuilder, oRCFGB, mRCFGB, LoggingLevel.WARN));
        oRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_ExternalSolver, Setting.SettingType.BOOLEAN,
                "external solver", "false", false));

        List<Setting> oTrAbs = new ArrayList<Setting>();
        List<Setting> mTrAbs = new ArrayList<Setting>();
        oTrAbs.add(new Setting("/Compute\\ Interpolants\\ along\\ a\\ Counterexample", Setting.SettingType.STRING,
                "interpolation", "Craig_NestedInterpolation", false));
        oTrAbs.add(new Setting("/Compute\\ Hoare\\ Annotation\\ of\\ negated\\ interpolant\\ automaton,\\ abstraction\\ and\\ CFG", Setting.SettingType.BOOLEAN,
                "Compute Hoare Annotation", "true", true));
        oTrAbs.add(new Setting("/Timeout", Setting.SettingType.INTEGER,
                "Timeout", "20", false));
        mTrAbs.add(new Setting("/DumpPath", Setting.SettingType.STRING,
                "Where to dump", "C:\\Code\\log\\dump", false));
        tools.add(new Tool(PrefStrings.s_traceAbstraction, oTrAbs, mTrAbs,
                LoggingLevel.WARN));
		return tools;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setPluginsLoggingLevel
	 * ()
	 */
	@Override
	protected LoggingLevel setPluginsLoggingLevel() {
		return LoggingLevel.INFO;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setToolsLoggingLevel
	 * ()
	 */
	@Override
	protected LoggingLevel setToolsLoggingLevel() {
		return LoggingLevel.INFO;
	}
}
