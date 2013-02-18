/**
 * This object represents a Tool within a toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Toolchain.LoggingLevel;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 05.03.2012
 */
public class Tool {
	/**
	 * The Ultimate ID for the tool.
	 */
	private String id;
	/**
	 * A list of user changeable settings for this tool.
	 */
	private List<Setting> optionalSettings;
	/**
	 * A list of fixed (not user changeable) settings.
	 */
	private List<Setting> mandatorySettings;
	/**
	 * The level of Ultimates output for this specific tool.
	 */
	private LoggingLevel loggingLevel;

	/**
	 * Constructor.
	 * 
	 * @param id
	 *            the ultimate id for this tool.
	 * @param optionalSettings
	 *            a list of user changeable settings for this tool.
	 * @param mandatorySettings
	 *            a list of fixed (not user changeable) settings.
	 * @param loggingLevel
	 *            the level of Ultimates output for this specific tool.
	 */
	public Tool(String id, List<Setting> optionalSettings,
			List<Setting> mandatorySettings, LoggingLevel loggingLevel) {
		this.id = id;
		this.optionalSettings = optionalSettings;
		this.mandatorySettings = mandatorySettings;
		this.loggingLevel = loggingLevel;
	}

	/**
	 * Getter for the ultimate id for this tool.
	 * 
	 * @return the unique Ultimate id for this tool.
	 */
	public String getId() {
		return id;
	}

	/**
	 * Getter for the identifier for this tool used on the website in HTML and
	 * JS code.
	 * 
	 * @return the identifier for this tool used on the website in HTML and JS
	 *         code.
	 */
	public String getHTMLId() {
		String s = id.replaceAll(
				"[^\\p{L}\\p{N}]", "");
		return s.substring(0, s.length()).toLowerCase();
	}

	/**
	 * Getter for the list of user changeable settings for this tool.
	 * 
	 * @return the user changeable settings
	 */
	public List<Setting> getUserChangeableSettings() {
		ArrayList<Setting> userchangeableSettings = new ArrayList<Setting>();
		for (Setting s : optionalSettings) {
			if (s.isUserModifiable()) {
				userchangeableSettings.add(s);
			}
		}
		for (Setting s : mandatorySettings) {
			if (s.isUserModifiable()) {
				userchangeableSettings.add(s);
			}
		}
		return userchangeableSettings;
	}
	
	/**
	 * Getter for the list of <i>not</i> user changeable settings for this tool.
	 * 
	 * @return the <i>not</i> user changeable settings
	 */
	public List<Setting> getFixedSettings() {
		ArrayList<Setting> fixedSettings = new ArrayList<Setting>();
		for (Setting s : optionalSettings) {
			if (!s.isUserModifiable()) {
				fixedSettings.add(s);
			}
		}
		for (Setting s : mandatorySettings) {
			if (!s.isUserModifiable()) {
				fixedSettings.add(s);
			}
		}
		return fixedSettings;
	}

	/**
	 * Getter for the list of mandatory settings.
	 * 
	 * @return the list of mandatory settings.
	 */
	public List<Setting> getMandatorySettings() {
		return mandatorySettings;
	}
	
	/**
	 * Getter for the list of optional settings.
	 * 
	 * @return the list of optional settings.
	 */
	public List<Setting> getOptionalSettings() {
		return optionalSettings;
	}

	/**
	 * Getter for the tools logging level.
	 * 
	 * @return a logging level.
	 */
	public Toolchain.LoggingLevel getLoggingLevel() {
		return this.loggingLevel;
	}
}
