/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.gui;

import java.awt.Rectangle;
import java.util.prefs.Preferences;

/**
 * Stores GUI settings.
 * @author Philipp
 *
 */
public class Settings {
	
	private static final int MAX_RECENT_FILES = 10;
	
	private static final Preferences prefs = Preferences.userNodeForPackage(Settings.class);
	
	/**
	 * Checks whether the main window is supposed to be maximized or not.
	 * @return true if maximized, false if not
	 */
	public static boolean getMainWindowMaximized(){
		return prefs.getBoolean("MainWindow/maximized", false);
	}
	/**
	 * Writes whether the main window is supposed to be maximized or not.
	 * @param max true if maximized, false if not
	 */
	public static void setMainWindowMaximized(boolean max){
		prefs.put("MainWindow/maximized", String.valueOf(max));
	}
	
	/**
	 * Reads the bounding rectangle of the main window.
	 * @return the bounding rectangle of the main window
	 */
	public static Rectangle getMainWindowRect(){
		return new Rectangle(prefs.getInt("MainWindow/left", 0),
							 prefs.getInt("MainWindow/top", 0),
							 prefs.getInt("MainWindow/width", 800),
							 prefs.getInt("MainWindow/height", 600));
		
	}
	/**
	 * Stores the bounding rectangle of the main window.
	 * @param rect the bounding rectangle of the main window
	 */
	public static void setMainWindowRect(Rectangle rect){
		prefs.put("MainWindow/left",  String.valueOf(rect.x));
		prefs.put("MainWindow/top",   String.valueOf(rect.y));
		prefs.put("MainWindow/width", String.valueOf(rect.width));
		prefs.put("MainWindow/height",String.valueOf(rect.height));
		
	}
	
	/**
	 * Reads the location of the splitter bar in the main window.
	 * @return the location of the splitter bar in the main window
	 */
	public static int getMainWindowSplitterLocation(){
		return prefs.getInt("MainWindow/splitter", 170);
	}
	/**
	 * Writes the location of the splitter bar in the main window.
	 * @param val the location of the splitter bar in the main window
	 */
	public static void setMainWindowSplitterLocation(int val){
		prefs.put("MainWindow/splitter", String.valueOf(val));
	}
	
	/**
	 * Reads the list of up to MAX_RECENT_FILES recently opened files.
	 * @return the list of up to MAX_RECENT_FILES recently opened files
	 */
	public static String[] getRecentFiles(){
		String recentFiles[] = new String[MAX_RECENT_FILES];
		for (int i = 0; i < MAX_RECENT_FILES; i++){
			String s = prefs.get("RecentFile" + i, "");
			recentFiles[i] = (s.length() != 0) ? s : null; 
		}
		return recentFiles;
	}
	/**
	 * Adds a filename to the top of the list of recently opened files.<br>
	 * If the filename is already in the list, it will be moved on top,
	 * otherwise a new entry will be added to the beginning of the list.
	 * @param filename filename to add
	 */
	public static  void addRecentFile(String filename){
		String[] oldRecent = getRecentFiles();
		String[] recent = new String[oldRecent.length];
	
		prefs.put("RecentFile" + 0 , filename);
		int d = 1;
		for (int i = 1; i < recent.length; i++){
			String s = oldRecent[i-d];
			if (filename.equals(s)){
				s = oldRecent[i];
				d = 0;
			}
			if (s == null) {
				prefs.remove("RecentFile" + i);
			} else {
				prefs.put("RecentFile" + i , s);
			}
		}
	}

	/**
	 * Clears the list of recent files.
	 */
	public static  void clearRecentFiles(){
		for (int i = 0; i < MAX_RECENT_FILES; i++){
			prefs.remove("RecentFile" + i);
		}
	}
	
}
