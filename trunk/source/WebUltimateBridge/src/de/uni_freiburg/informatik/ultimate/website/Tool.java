/**
 * This object represents a Tool within a toolchain.
 */
package de.uni_freiburg.informatik.ultimate.website;

/**
 * @author dietsch@informatik.uni-freiburg.de
 */
public class Tool {
	private final String mId;

	/**
	 * @param id
	 *            the Ultimate ID for this tool (i.e. the ID defined by IUltimatePlugin.getPluginID()).
	 */
	public Tool(final String id) {
		mId = id;
	}

	/**
	 * @return the unique Ultimate id for this tool (i.e. the ID defined by IUltimatePlugin.getPluginID()).
	 */
	public String getId() {
		return mId;
	}

	/**
	 * Getter for the identifier for this tool used on the website in HTML and JS code.
	 *
	 * @return the identifier for this tool used on the website in HTML and JS code.
	 */
	public String getHTMLId() {
		final String s = mId.replaceAll("[^\\p{L}\\p{N}]", "");
		return s.substring(0, s.length()).toLowerCase();
	}
}
