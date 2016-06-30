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
 * Script if control statement.
 * Usage:
 * if condition then
 * ...
 * else
 * ...
 * end
 * 
 * Else is optional
 * condition can by any expression, any resulting value that is not null or false is considered true (including 0!)
 * @author Philipp
 *
 */
public class If extends Statement {

	private Expression condition;
	private List<Statement> ifStatements;
	private List<Statement> elseStatements;
	
	/**
	 * Creates a new If expression.
	 * @param condition condition expression to evaluate
	 * @param ifStatements statements to execute if the condition is true
	 * @param elseStatements  statements to execute if the condition is false
	 */
	public If(Expression condition, List<Statement> ifStatements, List<Statement> elseStatements) {
		this.condition = condition;
		this.ifStatements = ifStatements;
		this.elseStatements = elseStatements;
	}

	@Override
	public ScriptObject execute(Environment env) {
		List<Statement> execStatements;
		if (this.condition.execute(env).isTrue()){
			execStatements = this.ifStatements;
		} else {
			execStatements = this.elseStatements;
		}
		ScriptObject ret = ScriptObject.nullValue;
		for (Statement stmt : execStatements){
			ret = stmt.execute(env);
		}
		return ret;
	}

}
