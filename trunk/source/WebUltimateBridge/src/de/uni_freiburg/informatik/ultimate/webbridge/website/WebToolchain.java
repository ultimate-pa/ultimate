/**
 * Represents a toolchain.
 */
package de.uni_freiburg.informatik.ultimate.webbridge.website;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting.SettingType;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public abstract class WebToolchain {

	private static final String SETTINGS_PATH_PREFIX =
			"/de/uni_freiburg/informatik/ultimate/webbridge/resources/settings/";
	private static final int MAX_LENGTH_NAME = 30;
	private static final int MAX_LENGTH_ID = 30;
	private static final int TIMEOUT_MS = 5 * 60 * 1000;
	private static final int MAX_LENGTH_DESCRIPTION = 250;
	private static final String EOL = System.getProperty("line.separator");
	private static final Set<String> IDS = new HashSet<>();

	/**
	 * @author Markus Lindenmann
	 * @author Oleksii Saukh
	 * @author Stefan Wissert
	 * @date 07.03.2012
	 */
	public enum LoggingLevel {
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

	private String mName;
	private String mId;
	private Tasks.TaskNames[] mTaskName;
	private String mUserInfo;
	private String mLayoutOrientation;
	private String mLayoutFontsize;
	private String mLayoutTransitions;
	private String mLanguage;
	private String mDescription;
	private List<Tool> mTools;
	private final List<Setting> mSettings;

	public WebToolchain() {
		setName(defineName());
		setId(defineId());
		setTaskName(defineTaskName());
		setDescription(defineDescription());
		setLanguage(defineLanguage());
		setInterfaceLayoutFontsize(defineInterfaceLayoutFontsize());
		setInterfaceLayoutOrientation(defineInterfaceLayoutOrientation());
		setInterfaceLayoutTransitions(defineInterfaceLayoutTransitions());
		setUserInfo(defineUserInfo());
		setTools(defineTools());

		mSettings = new ArrayList<>();
		createSettingsFromSettingsFile(defineToolchainSettingsFile());
		setAdditionalSettings(defineAdditionalSettings());

		if (mLanguage == null) {
			throw new IllegalArgumentException("defineLanguage() may not return null");
		}
	}

	/**
	 * Getter for the name of this toolchain.
	 *
	 * @return the name
	 */
	public final String getName() {
		return mName;
	}

	/**
	 * Getter for the task name.
	 *
	 * @return the names of the tasks, where this toolchain can be applied.
	 */
	public final Tasks.TaskNames[] getTaskName() {
		return mTaskName;
	}

	/**
	 * Getter for the toolchain ID.
	 *
	 * @return the unique id of this toolchain.
	 */
	public final String getId() {
		return mId;
	}

	/**
	 * Getter for the toolchains tools.
	 *
	 * @return an ordered list of tools that this toolchain executes.
	 */
	public final List<Tool> getTools() {
		return mTools;
	}

	/**
	 * Getter for the short description String.<br />
	 * <i>Might return the empty String, as this field is optional</i>
	 *
	 * @return a String describing this toolchain
	 */
	public final String getDescription() {
		return mDescription;
	}

	/**
	 * Getter for the toolchain XML String, listing the tools to call.
	 *
	 * @return the toolchain XML String
	 */
	public final String getToolchainXML() {
		final StringBuilder toolchainXml = new StringBuilder();
		toolchainXml.append("<rundefinition>").append(EOL);
		toolchainXml.append("<name>").append(getClass().getSimpleName()).append("</name>").append(EOL);
		toolchainXml.append("<toolchain>").append(EOL);
		for (final Tool t : mTools) {
			toolchainXml.append("\t<plugin id=\"");
			toolchainXml.append(t.getId());
			toolchainXml.append("\"/>").append(EOL);
		}
		toolchainXml.append("</toolchain></rundefinition>");
		return toolchainXml.toString();
	}

	/**
	 * Getter for the setting file.<br />
	 * This messages collects information about this toolchain and returns them in the format of an Ultimate settings
	 * file as a <b>String</b>.
	 *
	 * @return the content of a created settings file for this toolchain.
	 */
	public final String getSettingFileContent() {
		final DateFormat dateFormat = new SimpleDateFormat("EEE MMM dd HH:mm:ss z yyyy");
		final StringBuilder settings = new StringBuilder("#");
		settings.append(dateFormat.format(new Date())).append(EOL);
		settings.append("# Settings file for ").append(getId()).append(", ").append(getName()).append(EOL);
		settings.append(EOL).append("#").append(dateFormat.format(new Date()));
		settings.append(EOL).append("file_export_version=3.0").append(EOL);
		for (final Setting set : mSettings) {
			if (set.isUserModifiable()) {
				settings.append("# User-modifiable").append(EOL);
			}
			if ("".equals(set.getSettingString())) {
				settings.append("\\!");
			}
			settings.append("/instance/");
			settings.append(set.getSettingString());
			settings.append("=");
			settings.append(set.getSetValues());
			settings.append(EOL);
		}
		return settings.toString();
	}

	/**
	 * Setter for the toolchains description string.<br />
	 * <i>optional field: leave empty if not required.</i>
	 *
	 * @return the description
	 */
	protected abstract String defineDescription();

	/**
	 * Setter for the toolchains name.
	 *
	 * @return the name
	 */
	protected abstract String defineName();

	/**
	 * Setter for the toolchains id. ID must be unique and must not contain any spaces or symbols not contained in
	 * <code>(a-Z0-9)*</code>
	 *
	 * @return the id
	 */
	protected abstract String defineId();

	/**
	 * Setter for the task name.
	 *
	 * @return the task names
	 */
	protected abstract Tasks.TaskNames[] defineTaskName();

	/**
	 * Setter for the tools.
	 *
	 * @return the tools
	 */
	protected abstract List<Tool> defineTools();

	/**
	 * Setter for the language used on the website.
	 *
	 * @return the language string
	 */
	protected abstract String defineLanguage();

	/**
	 * Setter for layout font size for the interface on the website.
	 *
	 * @return the fontsize string
	 */
	protected String defineInterfaceLayoutFontsize() {
		return null;
	}

	/**
	 * Setter for layout orientation for the interface on the website.
	 *
	 * @return the orientation string
	 */
	protected String defineInterfaceLayoutOrientation() {
		return null;
	}

	/**
	 * Setter for layout transitions preset for the interface on the website.
	 *
	 * @return the transitions string
	 */
	protected String defineInterfaceLayoutTransitions() {
		return null;
	}

	/**
	 * Setter for the user info for this specific toolchain used on the website.
	 *
	 * @return the user info string
	 */
	protected String defineUserInfo() {
		return null;
	}

	/**
	 * @return the path to a settings file relative to resources.examples/ that should be loaded as default settings for
	 *         this tool, i.e. "LTLAutomizerC.epf", or null if no file should be loaded
	 */
	protected String defineToolchainSettingsFile() {
		return null;
	}

	/**
	 * @return a list of manually defined {@link Setting}s for this tool. They will override settings loaded by
	 *         {@link #defineToolchainSettingsFile()}. If the property {@link Setting#isUserModifiable()} is true, the
	 *         setting will be modifiable by the user from the settings menu of the website.
	 *
	 *         Per default, this method returns null.
	 */
	protected List<Setting> defineAdditionalSettings() {
		return Collections.emptyList();
	}

	/**
	 * Setter for the toolchains description string.<br />
	 * <i>optional field: leave empty if not required.</i>
	 *
	 * @param description
	 *            the description to set
	 */
	protected final void setDescription(final String description) {
		if (description == null) {
			mDescription = "";
			return;
		}
		if (description.length() > MAX_LENGTH_DESCRIPTION) {
			throw new IllegalArgumentException("String to long!");
		}
		mDescription = description;
	}

	/**
	 * Setter for the toolchains name.
	 *
	 * @param name
	 *            the name to set
	 */
	protected final void setName(final String name) {
		if (name == null || "".equals(name)) {
			throw new IllegalArgumentException("Name cannot be empty!");
		}
		if (name.length() > MAX_LENGTH_NAME) {
			throw new IllegalArgumentException("Name cannot be longer than " + MAX_LENGTH_NAME + " characters!");
		}
		mName = name;
	}

	/**
	 * Setter for the toolchains id. ID must be unique and must not contain any spaces or symbols not contained in
	 * <code>(a-Z0-9)*</code>
	 *
	 * @param id
	 *            the id to set
	 */
	protected final void setId(final String id) {
		if (id == null || "".equals(id)) {
			throw new IllegalArgumentException("ID cannot be empty!");
		}
		if (id.length() > MAX_LENGTH_ID) {
			throw new IllegalArgumentException("ID cannot be longer than " + MAX_LENGTH_ID + " characters!");
		}
		if (!id.matches("[a-z][a-zA-Z0-9]*")) {
			throw new IllegalArgumentException("ID must be element of (a-z)(a-Z0-9)*");
		}
		if (IDS.contains(id)) {
			throw new IllegalArgumentException("ID must be unique!");
		}
		IDS.add(id);
		mId = id;
	}

	/**
	 * Setter for the task name.
	 *
	 * @param taskName
	 *            the taskname to set
	 */
	protected final void setTaskName(final Tasks.TaskNames[] taskName) {
		mTaskName = taskName;
	}

	/**
	 * Setter for the language.
	 *
	 * @param language
	 *            the language string to set
	 */
	protected final void setLanguage(final String language) {
		mLanguage = language;
	}

	/**
	 * Setter for the interface font size on the website.
	 *
	 * @param mLanguage
	 *            the fontsize string to set
	 */
	protected final void setInterfaceLayoutFontsize(final String fontsize) {
		mLayoutFontsize = fontsize;
	}

	/**
	 * Setter for the interface orientation on the website.
	 *
	 * @param mLanguage
	 *            the orientation string to set
	 */
	protected final void setInterfaceLayoutOrientation(final String orientation) {
		mLayoutOrientation = orientation;
	}

	/**
	 * Setter for the interface transitions on the website.
	 *
	 * @param mLanguage
	 *            the transitions preset string to set
	 */
	protected final void setInterfaceLayoutTransitions(final String transition) {
		mLayoutTransitions = transition;
	}

	/**
	 * Setter for the user information shown on the website
	 *
	 * @return
	 */
	protected final void setUserInfo(final String userInfo) {
		mUserInfo = userInfo;
	}

	/**
	 * Setter for the tools list.
	 *
	 * @param tools
	 *            the tools
	 */
	private final void setTools(final List<Tool> tools) {
		if (tools == null) {
			throw new IllegalArgumentException("NULL is not a valid toolchain!");
		}
		if (tools.isEmpty()) {
			throw new IllegalArgumentException("Empty toolchain is not valid!");
		}
		mTools = tools;
	}

	private void createSettingsFromSettingsFile(final String defineToolchainSettingsFile) {
		if (defineToolchainSettingsFile == null) {
			return;
		}

		final String name = SETTINGS_PATH_PREFIX + defineToolchainSettingsFile;
		try {
			mSettings.addAll(readSettingsFromResource(name));
		} catch (final IOException e) {
			SimpleLogger.log("Exception occurred during loading of settings file for toolchain " + mId);
			e.printStackTrace();
		}

	}

	private List<Setting> readSettingsFromResource(final String resourceName) throws IOException {
		SimpleLogger.log("Loading settings file from " + getClass().getResource(resourceName) + " (ressourceName is "
				+ resourceName + ")");
		final InputStream stream = getClass().getResourceAsStream(resourceName);
		final BufferedReader buff = new BufferedReader(new InputStreamReader(stream));

		final List<Setting> rtr = new ArrayList<>();

		String line;
		while (true) {
			line = buff.readLine();
			if (line == null) {
				break;
			}
			if (line.startsWith("#")) {
				// ignore comments
				continue;
			}
			if (line.startsWith("@")) {
				// ignore versions
				continue;
			}
			if (line.startsWith("\\!")) {
				// ignore sections
				continue;
			}
			if (line.startsWith("/instance/")) {
				// we generate Settings from those lines

				final String[] valueName = splitAtEqualsSign(line).toArray(new String[0]);
				if (valueName.length != 2) {
					SimpleLogger.log("Ignoring line " + line);
					continue;
				}
				final String name = valueName[0].replaceFirst("/instance/", "");
				final String value = valueName[1];

				try {
					rtr.add(new Setting(name, SettingType.STRING, name, value, false));
				} catch (final Exception ex) {
					SimpleLogger.log("Exception occurred during creation of settings for line " + line);
					SimpleLogger.log(ex.getMessage());
				}
				continue;
			}
			SimpleLogger.log("Ignoring line " + line);
		}
		buff.close();
		return rtr;
	}

	private List<String> splitAtEqualsSign(final String line) {
		final List<String> rtr = new ArrayList<>();
		for (int i = 0; i < line.length(); ++i) {
			final char current = line.charAt(i);
			if (current == '=' && current > 0 && line.charAt(i - 1) != '\\') {
				rtr.add(line.substring(0, i));
				rtr.addAll(splitAtEqualsSign(line.substring(i + 1)));
				return rtr;
			}
		}
		rtr.add(line);
		return rtr;
	}

	private void setAdditionalSettings(final List<Setting> additionalSettings) {
		if (additionalSettings == null || additionalSettings.isEmpty()) {
			return;
		}
		// remove all settings that are already present
		for (final Setting setting : additionalSettings) {
			for (int i = 0; i < mSettings.size(); ++i) {
				if (setting.getSettingString().equals(mSettings.get(i).getSettingString())) {
					mSettings.remove(i);
					break;
				}
			}
		}
		mSettings.addAll(additionalSettings);
	}

	/**
	 * Getter for the user information shown on the website
	 *
	 * @return the user information
	 */
	public String getUserInfo() {
		return mUserInfo;
	}

	/**
	 * Getter for the language used on the website
	 *
	 * @return the toolchains language
	 */
	public String getLanguage() {
		return mLanguage;
	}

	/**
	 * Getter for the tools HTML layout fontsize.
	 *
	 * @return the fontsize.
	 */
	public String getInterfaceLayoutFontsize() {
		return mLayoutFontsize;
	}

	/**
	 * Getter for the tools HTML layout orientation.
	 *
	 * @return the orientation.
	 */
	public String getInterfaceLayoutOrientation() {
		return mLayoutOrientation;
	}

	/**
	 * Getter for the tools HTML layout transitions preset.
	 *
	 * @return the transitions preset.
	 */
	public String getInterfaceLayoutTransitions() {
		return mLayoutTransitions;
	}

	/**
	 *
	 * @return A default timeout in milliseconds for this toolchain. 0 means no timeout.
	 */
	public long getTimeout() {
		return TIMEOUT_MS;
	}

	public List<Setting> getUserModifiableSettings() {
		final List<Setting> rtr = new ArrayList<>();
		for (final Setting set : mSettings) {
			if (set.isUserModifiable()) {
				rtr.add(set);
			}
		}
		return rtr;
	}
}
