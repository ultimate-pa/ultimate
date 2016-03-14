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
 * While loop statement
 * @author Philipp
 *
 */
public class While extends Statement {

	private Expression condition;
	private List<Statement> statements;
	
	/**
	 * Creates a new While statement
	 * @param condition condition to check before every loop iteration.
	 * @param statements statements of the loop body.
	 */
	public While(Expression condition, List<Statement> statements) {
		this.condition = condition;
		this.statements = statements;
	}

	@Override
	public ScriptObject execute(Environment env) {
		try{
			while (this.condition.execute(env).isTrue()){
				for (Statement stmt : this.statements){
					stmt.execute(env);
				}
			}
			return ScriptObject.nullValue;
		} catch (Break.BreakException ex){
			return ScriptObject.nullValue;
		}
	}

}
