/*
 * Copyright (C) 2007-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2007-2015 bisser
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins;

import java.io.File;


/**
 * 
 * Note: 
 * 
 * @author  bisser
 */
public class Constants {
    private static String s_FileSeparator = ", ";
    private static final String s_PathSeparator = File.pathSeparator;

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
