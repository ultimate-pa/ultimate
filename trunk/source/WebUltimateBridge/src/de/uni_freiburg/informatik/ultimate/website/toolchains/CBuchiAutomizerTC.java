package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.Toolchain;


public class CBuchiAutomizerTC extends Toolchain {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setDescription()
	 */
	@Override
	protected String setDescription() {
		return "Büchi Automizer toolchain";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setName()
	 */
	@Override
	protected String setName() {
		return "BüchiAutomizer";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setId()
	 */
	@Override
	protected String setId() {
		return "cBuchiAutomizer";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTaskName()
	 */
	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.TERMINATION_C };
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
//      oCACSL.add(new Setting("/CheckedMethod", Setting.SettingType.STRING,
//              "Checked Method: ", "main", true));
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
		List<Setting> oRank = new ArrayList<Setting>();
		List<Setting> mRank = new ArrayList<Setting>();
        oRCFGB.add(new Setting("/HoareAnnotation", Setting.SettingType.BOOLEAN,
                "Compute Hoare Annotation", "false", true));
        oRCFGB.add(new Setting("/Timeout", Setting.SettingType.INTEGER,
                "Timeout", "20", false));
        oRCFGB.add(new Setting("/Determinization", "Type of Determinization",
        		new String[] { "EagerPost" }, false, new String[] {
              "LazyPost", "EagerPost", "Best Approximation" }, false));
        oRCFGB.add(new Setting("/BlockSize", "Type of Determinization",
        		new String[] { "sequence of program statements" }, false, new String[] {
              "sequence of program statements", "single program statement", "loop free block" }, false));
		tools.add(new Tool("BuchiAutomizer", oRank, mRank,
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
