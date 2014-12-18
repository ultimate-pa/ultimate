/**
 * This object represents a generalized toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.Collections;

/**
 * @author German Fordinal
 * @date 01.11.2014
 */
public class Worker {
	/**
	 * The HTML ID for the tool.
	 */
	private String id;
	/**
	 * The Ultimate ID for the tool.
	 */
	private String name;
	/**
	 * The website description of this worker.
	 */
	private String description;
	/**
	 * The websites execution button text.
	 */
	private String label;
	/**
	 * The websites user information to be displayed.
	 */
	private String userInfo;
	/**
	 * The websites layout orientation of the interface. "vertical", "horizontal"
	 */
	private String layoutOrientation;
	/**
	 * The websites font size of the interface. Any String of a number
	 */
	private String layoutFontsize;
	/**
	 * The websites transition preset of the interface. "true", "false"
	 */
	private String layoutTransitions;
	/**
	 * Where the content for the website is. optional.
	 */
	private String contentURL;
	/**
	 * Where the logo for the website is. optional.
	 */
	private String logoURL;
	/**
	 * The toochain collection of this worker.
	 */
	private ArrayList<WebToolchain> toolchains;
	/**
	 * The languages of this workers toolchains.
	 */
	private ArrayList<String> languages = new ArrayList<String>();
	/**
	 * Constructor.
	 * 
	 * @param name
	 *            the ultimate name for this toolchain collection.
	 * @param toolchains
	 *            a list of toolchains for this worker.
	 * @param label
	 *            the label to be shown on website to execute. Can be null
	 * @param description
	 *            the description for this worker on the website. Can be null
	 */
	public Worker(String name, String label, String description, ArrayList<WebToolchain> toolchains) {
		this.name              = name;
		this.label             = (label == null) ? getLabel(name) : label;
		this.description       = (description == null) ? getDescription(name) : description;
		this.toolchains        = (toolchains == null) ? new ArrayList<WebToolchain>() : toolchains;
		this.layoutFontsize    = null;
		this.layoutOrientation = null;
		this.layoutTransitions = null;
		setId(name);
	}

	/**
	 * Getter for a description for a specific worker-name.
	 * 
	 * @return the description of the name's matching worker.
	 */
	public String getDescription(String name) {
		if(description != null) return description;
		
		return "No description yet.";
	}
	
	/**
	 * overloading getDescription(String name) {}
	 * 
	 * @return
	 */
	public String getDescription() {
		return getDescription("");
	}

	/**
	 * Getter for a label for a specific worker-name.
	 * 
	 * @return the label of the name's matching worker.
	 */
	public String getLabel(String name) {
		if(label != null) return label;
		
		switch (name) {
		case "Trace Abstraction":
		case "Concurrent Trace Abstraction":
			  return "verify";
		case "BüchiAutomizer":
		case "Büchi Automizer":
			  return "analyze";
		case "LassoRanker":
		case "Lasso Ranker":
			  return "rank"; // synthesize?
		case "Automata Script":
			  return "run";
		default:
		  return "No description available";
		}
	}

	/**
	 * overloading getLabel(String name) {}
	 * 
	 * @return
	 */
	public String getLabel() {
		return getLabel("");
	}

	/**
	 * Adding a toolchain to this workers collection.
	 * 
	 * @return 
	 */
	public void addToolchain(WebToolchain toolchain) {
		if(toolchains.contains(toolchain)) return;
		toolchains.add(toolchain);
	}

	/**
	 * Getter for toolchains languages.
	 * 
	 * @return a list of languages
	 */
	public ArrayList<String> getLanguages() {
		if (languages.isEmpty()) {
			for (WebToolchain toolchain : toolchains) {
				if(!languages.contains(toolchain.getLanguage()))
					languages.add(toolchain.getLanguage());
			}
		}
		Collections.sort(languages);
		return languages;
	}

	/**
	 * Getter for the ultimate name for this worker.
	 * 
	 * @return the name for this worker.
	 */
	public String getName() {
		return name;
	}

	/**
	 * Getter for the html id for this worker.
	 * 
	 * @return the name for this worker.
	 */
	public String getId() {
		return id;
	}

	/**
	 * Setter for the html id for this worker.
	 * 
	 * @param name
	 * 			the Ultimate name of this worker
	 */
	public void setId(String name) {
		this.id = toKey(name);
	}

	/**
	 * Getter for the toolchain collection of this worker.
	 * 
	 * @return the list of toolchains for this worker.
	 */
	public ArrayList<WebToolchain> getToolchains() {
		return toolchains;
	}

	/**
	 * Getter for the html id for this worker.
	 * 
	 * @return the name for this worker.
	 */
	public String getUserInfo() {
		return userInfo;
	}

	/**
	 * Getter for the specific content URL for this worker
	 * 
	 * @return the url for this workers content json.
	 */
	public String getContentURL() {
		return contentURL;
	}

	/**
	 * Getter for the logo URL for this worker
	 * 
	 * @return the url for this workers content json.
	 */
	public String getLogoURL() {
		return logoURL;
	}

	public String getInterfaceLayoutFontsize() {
		return layoutFontsize;
	}

	public String getInterfaceLayoutOrientation() {
		return layoutOrientation;
	}

	public String getInterfaceLayoutTransitions() {
		return layoutTransitions;
	}

	/**
	 * Setter for the html userInfo for this worker.
	 * 
	 */
	public void setUserInfo(String userInfo) {
		this.userInfo = userInfo;
	}

	/**
	 * Setter for the html json content URL.
	 * 
	 */
	public void setContentURL(String url) {
		this.contentURL = url;
	}

	/**
	 * Setter for the html logo of this worker.
	 * 
	 */
	public void setLogoURL(String url) {
		this.logoURL = url;
	}

	/**
	 * Setter for the html fontsize preset of this worker.
	 * 
	 */
	public void setInterfaceLayoutFontsize(String fontsize) {
		this.layoutFontsize = fontsize;
	}

	/**
	 * Setter for the html orientation preset of this worker.
	 * 
	 */
	public void setInterfaceLayoutOrientation(String orientation) {
		this.layoutOrientation = orientation;
	}

	/**
	 * Setter for the html transitions usage preset of this worker.
	 * 
	 */
	public void setInterfaceLayoutTransitions(String transitions) {
		this.layoutTransitions = transitions;
	}

	/**
	 * Converts a given String to URL and HTML usable
	 * 
	 */
	public static String toKey(String name) {
		return name.toLowerCase().replaceAll("\\s+","_");
	}
}
