/**
 * C TraceAbstraction toolchain.
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
 * @author Matthias Heizmann
 * @date 14.02.2012
 */
public class CAutomizerTC extends WebToolchain {

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uni_freiburg.informatik.ultimate.website.Toolchain#setDescription()
     */
    @Override
    protected String setDescription() {
        return "Automizer toolchain";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setName()
     */
    @Override
    protected String setName() {
        return "Automizer";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setId()
     */
    @Override
    protected String setId() {
        return "cAutomizer";
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
     * @see de.uni_freiburg.informatik.ultimate.website.WebToolchain#setLanguage()
     */
    @Override
    protected String setLanguage() {
        return "c";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.WebToolchain#setUserInfo()
     */
    @Override
    protected String setUserInfo() {
        return "This is the user info";
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
        List<Setting> mCACSL = new ArrayList<Setting>();
        mCACSL.add(new Setting(PrefStrings.s_CACSL_LABEL_StartFunction, Setting.SettingType.STRING,
                "Starting procedure: ", "main", true));
        mCACSL.add(new Setting(PrefStrings.s_CACSL_LABEL_TranslationMode, "Translation Mode",
				new String[] { PrefStrings.s_CACSL_VALUE_Svcomp }, false, new String[] {
        		PrefStrings.s_CACSL_VALUE_Base, PrefStrings.s_CACSL_VALUE_Svcomp }, true));
        
        tools.add(new Tool(PrefStrings.s_cacsl2boogietranslator, oCACSL, mCACSL,
                LoggingLevel.WARN));
        tools.addAll(BoogieAutomizerTC.boogieTools());
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
