/*
 * Project:	de.uni_freiburg.informatik.ultimate.dev.eclipse.templates
 * Package:	de.uni_freiburg.informatik.ultimate.dev.eclipse.templates
 * File:	UltimatePluginData.java created on Feb 27, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.dev.eclipse.templates;

import java.util.List;

/**
 * UltimatePluginData
 * 
 * @author Björn Buchhold
 * 
 */
public class UltimatePluginData {

	/**
	 * String pluginId
	 */
	private String pluginId;

	/**
	 * String pluginName
	 */
	private String pluginName;

	/**
	 * String fileExtension
	 */
	private List<String> fileExtensions;

	public enum PluginType {
		analysis, generator, output, source
	};

	public enum QueryKeyword {
		ALL, USER, LAST, SOURCE, TOOL, ALLANDPERSIST
	};

	private PluginType type;

	private QueryKeyword queryKeyword;

	/**
	 * boolean managedObserver
	 */
	private boolean managedObserver;

	/**
	 * boolean requiresGui
	 */
	private boolean guiRequired;

	/**
	 * @param pluginId
	 * @param pluginName
	 * @param type
	 * @param managedObserver
	 */
	public UltimatePluginData(String pluginId, String pluginName,
			PluginType type, boolean managedObserver, boolean requiredGui,
			List<String> fileExtensions, QueryKeyword queryKeyword) {
		this.pluginId = pluginId;
		this.pluginName = pluginName;
		this.type = type;
		this.managedObserver = managedObserver;
		this.guiRequired = requiredGui;
		this.queryKeyword = queryKeyword;
		this.fileExtensions = fileExtensions;
	}

	/**
	 * getter for field managedObserver
	 * 
	 * @return the managedObserver
	 */
	public boolean isManagedObserver() {
		return this.managedObserver;
	}

	/**
	 * setter for field managedObserver
	 * 
	 * @param managedObserver
	 *            the managedObserver to set
	 */
	public void setManagedObserver(boolean managedObserver) {
		this.managedObserver = managedObserver;
	}

	/**
	 * getter for field type
	 * 
	 * @return the type
	 */
	public PluginType getType() {
		return this.type;
	}

	/**
	 * setter for field type
	 * 
	 * @param type
	 *            the type to set
	 */
	public void setType(PluginType type) {
		this.type = type;
	}

	/**
	 * getter for field pluginName
	 * 
	 * @return the pluginName
	 */
	public String getPluginName() {
		return this.pluginName;
	}

	/**
	 * setter for field pluginName
	 * 
	 * @param pluginName
	 *            the pluginName to set
	 */
	public void setPluginName(String pluginName) {
		this.pluginName = pluginName;
	}

	/**
	 * getter for field pluginId
	 * 
	 * @return the pluginId
	 */
	public String getPluginId() {
		return this.pluginId;
	}

	/**
	 * setter for field pluginId
	 * 
	 * @param pluginId
	 *            the pluginId to set
	 */
	public void setPluginId(String pluginId) {
		this.pluginId = pluginId;
	}

	/**
	 * Object getInterfaceName
	 * 
	 * @return
	 */
	public String getInterfaceName() {
		if (this.type == PluginType.analysis) {
			return "IAnalysis";
		}
		if (this.type == PluginType.generator) {
			return "IGenerator";
		}
		if (this.type == PluginType.source) {
			return "ISource";
		}
		return "IOutput";
	}

	/**
	 * Object getTypeString
	 * 
	 * @return
	 */
	public String getTypeString() {
		if (this.type == PluginType.analysis) {
			return "analysis";
		}
		if (this.type == PluginType.generator) {
			return "generator";
		}
		if (this.type == PluginType.source) {
			return "source";
		}
		return "output";
	}

	/**
	 * getter for field requiresGui
	 * 
	 * @return the requiresGui
	 */
	public boolean isGuiRequired() {
		return this.guiRequired;
	}

	/**
	 * setter for field requiresGui
	 * 
	 * @param requiresGui
	 *            the requiresGui to set
	 */
	public void setGuiRequired(boolean requiresGui) {
		this.guiRequired = requiresGui;
	}

	/**
	 * getter for field queryKeyword
	 * 
	 * @return the queryKeyword
	 */
	public QueryKeyword getQueryKeyword() {
		return this.queryKeyword;
	}

	public String getQueryKeywordString() {
		return "QueryKeyword." + getQueryKeyword();
	}

	/**
	 * setter for field queryKeyword
	 * 
	 * @param queryKeyword
	 *            the queryKeyword to set
	 */
	public void setQueryKeyword(QueryKeyword queryKeyword) {
		this.queryKeyword = queryKeyword;
	}

	/**
	 * getter for field fileExtensions
	 * 
	 * @return the fileExtensions
	 */
	public List<String> getFileExtensions() {
		return this.fileExtensions;
	}

	/**
	 * setter for field fileExtensions
	 * 
	 * @param fileExtensions
	 *            the fileExtensions to set
	 */
	public void setFileExtensions(List<String> fileExtensions) {
		this.fileExtensions = fileExtensions;
	}

	/**
	 * @return
	 */
	public String getCommaSepFileTypeStrings() {
		StringBuffer sb = new StringBuffer();
		for (String fe : this.fileExtensions) {
			sb.append("\"");
			sb.append(fe);
			sb.append("\", ");
		}
		sb.delete(sb.length() - 2, sb.length());
		return sb.toString();
	}
}
