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
package de.uni_muenster.cs.sev.lethal.script.exceptions;

/**
 * Exception raised by the parser when it fails to read the script.
 * @author Philipp
 *
 */
public class ScriptParseException extends RuntimeException {
	
	private int line;
	
	/**
	 * Creates a ScriptParseException
	 * @param line text line the error occurred in.
	 * @param message error message.
	 */
	public ScriptParseException(int line , String message){
		super("Line " + line + ": " + message);
    this.line = line;
  }

	/**
	 * returns the script line the ParseException occurred in.
	 * @return the script line the ParseException occurred in.
	 */
	public int getLine() {
		return line;
	}
	
}
