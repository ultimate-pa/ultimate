/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

/**
 * File I/O
 * 
 * @author arlt
 */
public class FileIO {

	/**
	 * Reads text from a file
	 * 
	 * @param filename
	 *            File name
	 * @return null = failure
	 */
	public static String fromFile(String filename) {
		String s = null;
		try {
			StringBuffer sb = new StringBuffer();
			FileReader fr = new FileReader(new File(filename));
			BufferedReader br = new BufferedReader(fr);

			while (null != (s = br.readLine())) {
				sb.append(s + "\r\n");
			}

			s = sb.toString();
			fr.close();

		} catch (IOException e) {
			e.printStackTrace();
			s = null;
		}
		return s;
	}

	/**
	 * Writes text to a file
	 * 
	 * @param text
	 *            Text
	 * @param filename
	 *            File name
	 * @return false = failure
	 */
	public static boolean toFile(String text, String filename) {
		boolean success = false;
		try {
			FileWriter fw = new FileWriter(new File(filename));
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write(text);
			bw.close();
			fw.close();
			success = true;
		} catch (IOException e) {
			e.printStackTrace();
		}
		return success;
	}

	/**
	 * Checks if the directory exists
	 * 
	 * @param dirname
	 *            directory name
	 * @return true = directory does exist
	 */
	public static boolean doesDirectoryExist(String dirname) {
		if (null == dirname) {
			return false;
		}

		File file = new File(dirname);
		return file.exists() && file.isDirectory();
	}

	/**
	 * Checks if the file exists
	 * 
	 * @param filename
	 *            File name
	 * @return true = file does exist
	 */
	public static boolean doesFileExist(String filename) {
		if (null == filename) {
			return false;
		}

		File file = new File(filename);
		return file.exists() && file.isFile();
	}

	/**
	 * Checks if the file's path exists
	 * 
	 * @param filename
	 *            File name
	 * @return true = file's path does exist
	 */
	public static boolean doesDirectoryOfFileExist(String filename) {
		if (null == filename) {
			return false;
		}

		File file = new File(filename);
		File fileParent = file.getParentFile();

		if (null == fileParent) {
			return false;
		}

		return fileParent.exists();
	}

	/**
	 * Finds files in a directory
	 * 
	 * @param dirName
	 *            Directory name
	 * @param fileName
	 *            File name
	 * @return Found files
	 */
	public static String[] findFiles(String dirName, String fileName) {
		List<String> files = new ArrayList<String>();
		findFiles(dirName, fileName, files);
		return files.toArray(new String[files.size()]);
	}

	/**
	 * Finds files in a directory
	 * 
	 * @param dirName
	 *            Directory name
	 * @param fileName
	 *            File name
	 * @param files
	 *            List of files
	 */
	protected static void findFiles(String dirName, String fileName,
			List<String> files) {
		try {
			File dir = new File(dirName);
			for (File file : dir.listFiles()) {
				if (file.isDirectory()) {
					findFiles(file.getPath(), fileName, files);
				} else if (file.isFile()) {
					if (file.getName().equals(fileName)) {
						files.add(file.getPath());
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Generates a temporary filename
	 * 
	 * @param ext
	 *            Extension of the filename
	 * @return Temporary filename
	 */
	public static String generateTempFileName(String ext) {
		return String.format("%s%s.%s", System.getProperty("java.io.tmpdir"),
				UUID.randomUUID().toString(), ext);
	}

}
