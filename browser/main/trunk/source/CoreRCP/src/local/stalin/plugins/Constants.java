package local.stalin.plugins;

import java.io.File;

import local.stalin.model.UniversalTokens;

/**
 * 
 * Note: 
 * 
 * @author  bisser
 */
public class Constants {
    private static String s_LoggerPattern = "%d{ISO8601} %-5p [%F:%L]: %m%n";
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
	 * @return  the lOG4J_PATTERN
	 * @uml.property  name="lOG4J_PATTERN"
	 */
    public static String getLoggerPattern() {
        return s_LoggerPattern;
    }

    /**
	 * @param log4j_pattern  the lOG4J_PATTERN to set
	 * @uml.property  name="lOG4J_PATTERN"
	 */
    public static void setLoggerPattern(String log4j_pattern) {
        s_LoggerPattern = log4j_pattern;
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
