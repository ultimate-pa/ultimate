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
package de.uni_muenster.cs.sev.lethal.script;

import java.util.List;

/**
 * Definition statement for user classes "class foobar \n ... \n end"
 * @author Philipp
 *
 */
public class ClassDefinition extends Statement {

	List<Statement> statements;
	String name;
	
	/**
	 * New class definition instance
//	 * @param parentEnvironment enclosing environment
//	 * @param classEnvironment  environment of the class to define (must be a direct child of parentEnvironment)
	 * @param name name of the class
	 * @param statements statements inside the class body.
	 */
	public ClassDefinition(String name, List<Statement> statements){
		this.statements = statements;
		this.name = name;
	}
	
	@Override
	public ScriptObject execute(Environment env) {
		Environment classEnvironment = env.newFrame();
		for (Statement statement : this.statements){
			statement.execute(classEnvironment);
		}
		env.bindLocal(name, new UserClass(name, null, classEnvironment));
		return ScriptObject.nullValue;
	}

}
