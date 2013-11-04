package de.uni_freiburg.informatik.ultimate.plugins;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.model.UniversalTokens;

/**
 * 
 * Note: 
 * 
 * @author  bisser
 */
public class Constants {
    private static String s_FileSeparator = ", ";
    private static String s_UndefinedTokenName = UniversalTokens.UNDEFINED.toString();
    private static final String s_PathSeparator = File.pathSeparator;

    /**
	 * @return  the tokenUndefined
	 * @uml.property  name="tokenUndefined"
	 */
    public static String getTokenUndefined() {
    	return s_UndefinedTokenName;
    }

    /**
	 * @param tokenUndefined  the tokenUndefined to set
	 * @uml.property  name="tokenUndefined"
	 */
    public static void setTokenUndefined(String tokenUndefined) {
        s_UndefinedTokenName = tokenUndefined;
    }


    /**
     * Gets a separator for files, this is just cosmetic
     * @return the separator
     */
    public static String getFileSep() {
        return s_FileSeparator;
    }

    /**
     * Sets a file separator for cosmetic purposes
     * @param file_sep
     */
    public static void setFileSep(String file_sep) {
        s_FileSeparator = file_sep;
    }

	/**
	 * returns the system path separator
	 * @return the pathSeparator
	 */
	public static String getPathSeparator() {
		return s_PathSeparator;
	}

}
