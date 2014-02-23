/**
 * Represents a toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public abstract class Toolchain {
	/**
	 * Timeout used for all toolchains.
	 */
	private static final int s_TimeoutInSeconds = 20;
	
	/**
	 * String that identifies the timeout setting from the core preferences.
	 */
	private static final String s_TimeoutString = 
			"Toolchain\\ timeout\\ in\\ seconds";
	/**
	 * The toolchain name to be shown on the website.
	 */
	private String name;
	/**
	 * The toolchain ID to identify this toolchain uniquely.
	 */
	private String id;
	/**
	 * Set of IDs to check uniqueness of IDs.
	 */
	private static final Set<String> ids = new HashSet<String>();
	/**
	 * The corresponding task name to be shown on the website.
	 */
	private Tasks.TaskNames[] taskName;
	/**
	 * Short String describing this toolchain.
	 */
	private String description;
	/**
	 * The tool list describing the toolchain.
	 */
	private List<Tool> tools;
	/**
	 * End of line separator. This depends on Ultimate and not the server - so
	 * one might have to change this accordingly lateron!
	 */
	private static final String EOL = System.getProperty("line.separator");
	/**
	 * The tools logging level.
	 */
	private LoggingLevel toolsLoggingLevel;
	/**
	 * The plugins logging level.
	 */
	private LoggingLevel pluginsLoggingLevel;

	/**
	 * @author Markus Lindenmann
	 * @author Oleksii Saukh
	 * @author Stefan Wissert
	 * @date 07.03.2012
	 */
	public static enum LoggingLevel {
		/**
		 * Debug logging level - all messages will be printed.
		 */
		DEBUG,
		/**
		 * Info logging level - all messages except debug will be printed.
		 */
		INFO,
		/**
		 * Warn logging level - only warnings and errors will be printed.
		 */
		WARN,
		/**
		 * Error logging level - only errors will be printed.
		 */
		ERROR
	}

	/**
	 * Constructor.
	 */
	public Toolchain() {
		this.setName(setName());
		this.setId(setId());
		this.setTaskName(setTaskName());
		this.setDescription(setDescription());
		this.setTools(setTools());
		this.setToolsLoggingLevel(setToolsLoggingLevel());
		this.setPluginsLoggingLevel(setPluginsLoggingLevel());
	}

	/**
	 * Getter for the name of this toolchain.
	 * 
	 * @return the name
	 */
	public final String getName() {
		return name;
	}

	/**
	 * Getter for the task name.
	 * 
	 * @return the names of the tasks, where this toolchain can be applied.
	 */
	public final Tasks.TaskNames[] getTaskName() {
		return taskName;
	}

	/**
	 * Getter for the toolchain ID.
	 * 
	 * @return the unique id of this toolchain.
	 */
	public final String getId() {
		return id;
	}
	
	/**
	 * Getter for the toolchains tools.
	 * 
	 * @return an ordered list of tools that this toolchain executes.
	 */
	public final List<Tool> getTools() {
		return tools;
	}

	/**
	 * Getter for the short description String.<br />
	 * <i>Might return the empty String, as this field is optional</i>
	 * 
	 * @return a String describing this toolchain
	 */
	public final String getDescription() {
		return this.description;
	}

	/**
	 * Getter for the toolchain XML String, listing the tools to call.
	 * 
	 * @return the toolchain XML String
	 */
	public final String getToolchainXML() {
		StringBuffer toolchainXML = new StringBuffer("<toolchain>");
		toolchainXML.append(EOL);
		for (Tool t : tools) {
			toolchainXML.append("\t<plugin id=\"");
			toolchainXML.append(t.getId());
			toolchainXML.append("\"/>").append(EOL);
		}
		toolchainXML.append("</toolchain>");
		return toolchainXML.toString();
	}
	
	public static final String s_LABEL_LogLevelPlugins = "Log\\ Level\\ for\\ Plugins";

	/**
	 * Given preference foo and value 0, this method returns the String
	 * /instance/UltimateCore/foo=0
	 * with a line separator at the end.
	 */
	private static String buildCoreSettingString(String preference, String value) {
		StringBuilder sb = new StringBuilder();
		sb.append("/instance/UltimateCore/");
		sb.append(preference).append("=").append(value).append(EOL);
		return sb.toString();
	}
	/**
	 * Getter for the setting file.<br />
	 * This messages collects information about this toolchain and returns them
	 * in the format of an Ultimate settings file as a <b>String</b>.
	 * 
	 * @return the content of a created settings file for this toolchain.
	 */
	public final String getSettingFile() {
		DateFormat dateFormat = new SimpleDateFormat(
				"EEE MMM dd HH:mm:ss z yyyy");
		StringBuffer settings = new StringBuffer("#");
		settings.append(dateFormat.format(new Date())).append(EOL);
		settings.append("# Settings file for ").append(getId()).append(", ")
				.append(getName()).append(EOL);
		settings.append("file_export_version=3.0").append(EOL);
		settings.append("\\!/instance/UltimateCore=").append(EOL);
		settings.append("@UltimateCore=1.0.0").append(EOL);
		settings.append(buildCoreSettingString(s_TimeoutString, String.valueOf(s_TimeoutInSeconds)));
		settings.append(buildCoreSettingString("Root\\ Log\\ Level", "INFO"));
		
		settings.append(buildCoreSettingString("Log\\ Level\\ for\\ Core\\ Plugin", "WARN"));
		settings.append(buildCoreSettingString("Log\\ Level\\ for\\ Plugins", getPluginsLoggingLevel()));
		settings.append(buildCoreSettingString("Log\\ Level\\ for\\ External\\ Tools", "WARN"));
		settings.append(buildCoreSettingString("Log\\ Level\\ for\\ Controller\\ Plugin", "INFO"));
		settings.append(buildCoreSettingString("Create\\ a\\ Logfile", "true"));
		settings.append(buildCoreSettingString("Append\\ to\\ exisiting\\ Logfile", "true"));
		settings.append(buildCoreSettingString("Name\\ of\\ the\\ Logfile", "Kandersteg"));

		for (Tool t : tools) {
			settings.append(t.getId()).append("\\=");
			settings.append(t.getLoggingLevel());
		}
		settings.append(EOL).append("#").append(dateFormat.format(new Date()));
		settings.append(EOL).append("file_export_version=3.0").append(EOL);
		settings.append("# Fixed settings:").append(EOL);
		for (Tool t : tools) {
			for (Setting s : t.getFixedSettings()) {
				if(s.getSettingString().equals("")) {
					settings.append("\\!");
				}
				settings.append("/instance/");
				settings.append(t.getId());
				settings.append("/");
				settings.append(s.getSettingString());
				settings.append("=");
				settings.append(s.getSetValues());
				settings.append(EOL);
			}
		}
		settings.append("# User changeable settings:").append(EOL);
		for (Tool t : tools) {
			for (Setting s : t.getUserChangeableSettings()) {
				settings.append("/instance/");
				settings.append(t.getId());
				settings.append("/");
				settings.append(s.getSettingString());
				settings.append("=");
				settings.append(s.getSetValues());
				settings.append(EOL);
			}
		}
		return settings.toString();
	}

	/**
	 * Getter for the plugins logging level.
	 * 
	 * @return the plugins logging level.
	 */
	private String getPluginsLoggingLevel() {
		return this.pluginsLoggingLevel.toString();
	}

	/**
	 * Getter for the tools logging level.
	 * 
	 * @return the tools logging level.
	 */
	private String getToolsLoggingLevel() {
		return this.toolsLoggingLevel.toString();
	}

	/**
	 * Setter for the general lugins logging level.
	 * 
	 * @return the plugins logging level.
	 */
	protected abstract LoggingLevel setPluginsLoggingLevel();

	/**
	 * Setter for the general tools logging level.
	 * 
	 * @return the tools logging level.
	 */
	protected abstract LoggingLevel setToolsLoggingLevel();

	/**
	 * Setter for the toolchains description string.<br />
	 * <i>optional field: leave empty if not required.</i>
	 * 
	 * @return the description
	 */
	protected abstract String setDescription();

	/**
	 * Setter for the toolchains name.
	 * 
	 * @return the name
	 */
	protected abstract String setName();

	/**
	 * Setter for the toolchains id. ID must be unique and must not contain any
	 * spaces or symbols not contained in <code>(a-Z0-9)*</code>
	 * 
	 * @return the id
	 */
	protected abstract String setId();

	/**
	 * Setter for the task name.
	 * 
	 * @return the task names
	 */
	protected abstract Tasks.TaskNames[] setTaskName();

	/**
	 * Setter for the tools.
	 * 
	 * @return the tools
	 */
	protected abstract List<Tool> setTools();

	/**
	 * Setter for the toolchains description string.<br />
	 * <i>optional field: leave empty if not required.</i>
	 * 
	 * @param description
	 *            the description to set
	 */
	protected final void setDescription(String description) {
		if (description == null) {
			description = "";
		}
		if (description.length() > 250) {
			throw new IllegalArgumentException("String to long!");
		}
		this.description = description;
	}

	/**
	 * Setter for the toolchains name.
	 * 
	 * @param name
	 *            the name to set
	 */
	protected final void setName(String name) {
		if (name == null || name.equals("")) {
			throw new IllegalArgumentException("Name cannot be empty!");
		}
		if (name.length() > 30) {
			throw new IllegalArgumentException(
					"Name cannot be longer than 30 characters!");
		}
		this.name = name;
	}

	/**
	 * Setter for the toolchains id. ID must be unique and must not contain any
	 * spaces or symbols not contained in <code>(a-Z0-9)*</code>
	 * 
	 * @param id
	 *            the id to set
	 */
	protected final void setId(String id) {
		if (id == null || id.equals("")) {
			throw new IllegalArgumentException("ID cannot be empty!");
		}
		if (id.length() > 30) {
			throw new IllegalArgumentException(
					"ID cannot be longer than 30 characters!");
		}
		if (!id.matches("[a-z][a-zA-Z0-9]*")) {
			throw new IllegalArgumentException(
					"ID must be element of (a-z)(a-Z0-9)*");
		}
		if (ids.contains(id)) {
			throw new IllegalArgumentException("ID must be unique!");
		}
		ids.add(id);
		this.id = id;
	}

	/**
	 * Setter for the task name.
	 * 
	 * @param taskName
	 *            the taskname to set
	 */
	protected final void setTaskName(Tasks.TaskNames[] taskName) {
		this.taskName = taskName;
	}

	/**
	 * Setter for the tools list.
	 * 
	 * @param tools
	 *            the tools
	 */
	protected final void setTools(List<Tool> tools) {
		if (tools == null) {
			throw new IllegalArgumentException("NULL is not a valid toolchain!");
		}
		if (tools.isEmpty()) {
			throw new IllegalArgumentException("Empty toolchain is not valid!");
		}
		this.tools = tools;
	}

	/**
	 * Setter for the tools logging level.
	 * 
	 * @param setToolsLoggingLevel
	 *            the general tools logging level.
	 */
	private void setToolsLoggingLevel(LoggingLevel setToolsLoggingLevel) {
		this.toolsLoggingLevel = setToolsLoggingLevel;
	}

	/**
	 * Setter for the plugins logging level.
	 * 
	 * @param setPluginsLoggingLevel
	 *            the general plugins logging level.
	 */
	private void setPluginsLoggingLevel(LoggingLevel setPluginsLoggingLevel) {
		this.pluginsLoggingLevel = setPluginsLoggingLevel;
	}
}
