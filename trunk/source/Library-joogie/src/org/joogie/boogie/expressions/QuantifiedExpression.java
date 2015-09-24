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

package org.joogie.boogie.expressions;

import java.util.LinkedList;
import java.util.List;

import org.joogie.boogie.types.BoogieType;

/**
 * @author schaef
 */
public class QuantifiedExpression extends Expression {

	private LinkedList<Variable> boundVars;
	private Expression termExpression;
	private Quantifier quant;

	public enum Quantifier {
		Exist("exists "), ForAll("forall ");

		private String description;

		Quantifier(String des) {
			description = des;
		}

		@Override
		public String toString() {
			return description;
		}

	}

	public QuantifiedExpression(Quantifier q, List<Variable> bound,
			Expression term) {
		quant = q;
		this.boundVars = new LinkedList<Variable>(bound);
		this.termExpression = term;
		// double check that the boundflag is set for the bound variables
		for (Variable v : this.boundVars)
			v.isBound = true;
	}

	public Expression getExpression() {
		return this.termExpression;
	}

	public LinkedList<Variable> getBoundVariables() {
		return this.boundVars;
	}

	public Quantifier getQuantifier() {
		return this.quant;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#toBoogie()
	 */
	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		if (this.quant == Quantifier.Exist) {
			sb.append("exists ");
		} else if (this.quant == Quantifier.ForAll) {
			sb.append("forall ");
		}
		boolean firstround = true;
		for (Variable v : this.boundVars) {
			if (firstround) {
				firstround = false;
			} else {
				sb.append(", ");
			}
			sb.append(v.toBoogie());
			sb.append(" : ");
			sb.append(v.getType().toBoogie());
		}
		sb.append(" :: ");
		sb.append(this.termExpression.toBoogie());
		sb.append(")");
		return sb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#getType()
	 */
	@Override
	public BoogieType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#clone()
	 */
	@Override
	public Expression clone() {
		LinkedList<Variable> clones = new LinkedList<Variable>();
		for (Variable v : this.boundVars)
			clones.add(v.clone());
		return new QuantifiedExpression(this.quant, clones,
				this.termExpression.clone());
	}

	public List<Variable> getUsedVariables() {
		LinkedList<Variable> ret = new LinkedList<Variable>();
		for (Variable v : this.termExpression.getUsedVariables()) {
			if (!this.boundVars.contains(v)) {
				ret.add(v);
			}
		}
		return ret;
	}

}
