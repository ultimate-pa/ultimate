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
 * @date 26.03.2013
 */
public class AutomtaScriptTC extends Toolchain {

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uni_freiburg.informatik.ultimate.website.Toolchain#setDescription()
     */
    @Override
    protected String setDescription() {
        return "Automata Script toolchain";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setName()
     */
    @Override
    protected String setName() {
        return "Automata Script";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setId()
     */
    @Override
    protected String setId() {
        return "automataScript";
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTaskName()
     */
    @Override
    protected TaskNames[] setTaskName() {
        return new TaskNames[] { TaskNames.AUTOMATA_SCRIPT };
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
        List<Setting> mCACSL = new ArrayList<Setting>();
        tools.add(new Tool("AutomataScriptInterpreter", oCACSL, mCACSL,
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
