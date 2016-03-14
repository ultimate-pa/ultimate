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

/**
 * Return Statement for aborting methods (not blocks!)
 * @author Philipp
 *
 */
public class Return extends Statement{

	private Expression returnExpression;
	
	/**
	 * Creates a new Return statement
	 * @param returnExpression expression to evaluate when executed.
	 */
	public Return(Expression returnExpression) {
		this.returnExpression = ((returnExpression == null) ? NullObject.nullObject : returnExpression);
	}

	@Override
	public ScriptObject execute(Environment env) {
		throw new ReturnException(returnExpression.execute(env));
	}

	/**
	 * Exception thrown when the return Statement is executed. To be catched in Method objects.
	 * @author Philipp
	 *
	 */
	public class ReturnException extends RuntimeException{
		private ScriptObject returnValue;
		
		/**
		 * Create a new ReturnException instance with the given method return value
		 * @param returnValue value the method should return
		 */
		public ReturnException(ScriptObject returnValue) {
			super();
			this.returnValue = returnValue;
		}

		/**
		 * Gets the method return value stored in this return exception
		 * @return the method return value stored in this return exception
		 */
		public ScriptObject getReturnValue() {
			return returnValue;
		}
		
		
	}
	
}
