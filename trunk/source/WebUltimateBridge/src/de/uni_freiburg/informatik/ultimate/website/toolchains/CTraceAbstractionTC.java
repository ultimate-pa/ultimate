/**
 * C TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.Toolchain;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public class CTraceAbstractionTC extends Toolchain {

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
        return "cTraceAbstraction";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTaskName()
     */
    @Override
    protected TaskNames[] setTaskName() {
        return new TaskNames[] { TaskNames.VerifyC };
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTools()
     */
    @Override
    protected List<Tool> setTools() {
        List<Tool> tools = new ArrayList<Tool>();
        List<Setting> oCACSL = new ArrayList<Setting>();
        oCACSL.add(new Setting("/CheckedMethod", Setting.SettingType.STRING,
                "Starting procedure: ", "main", true));
        oCACSL.add(new Setting("/Translation-Mode", "Translation Mode",
				new String[] { "Best SV_COMP" }, false, new String[] {
						"BASE", "SV_COMP" }, true));
        List<Setting> mCACSL = new ArrayList<Setting>();
        tools.add(new Tool("CACSL2BoogieTranslator", oCACSL, mCACSL,
                LoggingLevel.WARN));

        List<Setting> oPre = new ArrayList<Setting>();
        List<Setting> mPre = new ArrayList<Setting>();
        tools.add(new Tool(
                "de.uni_freiburg.informatik.ultimate.boogie.preprocessor",
                oPre, mPre, LoggingLevel.WARN));

        List<Setting> oRCFGB = new ArrayList<Setting>();
        List<Setting> mRCFGB = new ArrayList<Setting>();
        tools.add(new Tool("RCFGBuilder", oRCFGB, mRCFGB, LoggingLevel.WARN));

        List<Setting> oTrAbs = new ArrayList<Setting>();
//        oTrAbs.add(new Setting("", Setting.SettingType.STRING, "Mode",
//                "StrongestPost", true));
//        oTrAbs.add(new Setting("/AllErrorsAtOnce", Setting.SettingType.BOOLEAN,
//        		"check all specifications at once", "false", true));
//        oTrAbs.add(new Setting("/Minimize", Setting.SettingType.BOOLEAN,
//                "Use Minimization", "true", true));
        oRCFGB.add(new Setting("/HoareAnnotation", Setting.SettingType.BOOLEAN,
                "Compute Hoare Annotation", "true", true));
        oRCFGB.add(new Setting("/Timeout", Setting.SettingType.INTEGER,
                "Timeout", "300", false));
//        oTrAbs.add(new Setting("/Edges2True", Setting.SettingType.BOOLEAN,
//                "Edges to true", "true", true));
//        oTrAbs.add(new Setting("/Interpolants", Setting.SettingType.STRING,
//                "Which locations", "All locations", true));
//        oTrAbs.add(new Setting("/Determinization", "Type of Determinization",
//                new String[] { "Best Approximation" }, false, new String[] {
//                        "LazyPost", "EagerPost", "Best Approximation",
//                        "Add as many selfloops as possible" }, true));
        List<Setting> mTrAbs = new ArrayList<Setting>();
        mTrAbs.add(new Setting("/DumpPath", Setting.SettingType.STRING,
                "Where to dump", "C:\\Code\\log\\dump", false));
        tools.add(new Tool("TraceAbstraction", oTrAbs, mTrAbs,
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
