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

import java.awt.Image;
import java.awt.Toolkit;
import java.net.URL;

import javax.swing.ImageIcon;

/**
 * Common resource for loading functions.
 * @author Philipp
 *
 */
public class Resources {

	/**
	 * Loads an icon from the system resources.
	 * @param name filename of the icon to load
	 * @return icon object or null if the icon was not found
	 */
	public static ImageIcon loadIcon(String name){
		URL url = ClassLoader.getSystemResource(name);
		if (url != null) return new ImageIcon(url);
		return null;
	}
	
	/**
	 * Loads an image from the system resources.
	 * @param name filename of the icon to load
	 * @return image object or null if the image was not found
	 */
	public static Image loadImage(String name){
		URL url = ClassLoader.getSystemResource(name);
		if (url != null) return Toolkit.getDefaultToolkit().getImage(url);
		return null;
	}
	
}
