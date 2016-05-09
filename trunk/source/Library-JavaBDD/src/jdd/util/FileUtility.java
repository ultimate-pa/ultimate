
package jdd.util;

import java.util.*;
import java.io.*;

/**
 * Utility functions related to files are gathered here
 *
 */
public class FileUtility {

	/**
	 * returns true if the filename contains something we don't like,
	 * such as shell characters.
	 */
	public static boolean invalidFilename(String file) {

		// lets say \xxx is only invalid if we are not using windows ??
		if(File.separatorChar != '\\' && file.indexOf('\\') != -1 )
			return false;

		return
			file.indexOf('\"') != -1 ||			file.indexOf('\'') != -1 ||
			file.indexOf(';') != -1 ||			file.indexOf('&') != -1 ||
			file.indexOf('|') != -1 ||			file.indexOf('>') != -1 ||
			file.indexOf('<') != -1 ||			file.indexOf('#') != -1
			;

	}

	/**
	 * Delete a file.
	 * @return true if deletion succeeded
	 */
	public static boolean delete(String filename) {
		File f = new File(filename);
		return f.delete();
	}


}