/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Cookiefy plug-in.
 * 
 * The ULTIMATE Cookiefy plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Cookiefy plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Cookiefy plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Cookiefy plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Cookiefy plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;

/**
 * general helper methods
 * 
 */
public class Helper {

	/**
	 * Concatenates two Statement Arrays.
	 * 
	 * @param stmtArray1
	 * @param stmtArray2
	 * @return
	 */
	static Statement[] concatStatements(Statement[] stmtArray1,
			Statement[] stmtArray2) {
		final Statement[] result = new Statement[stmtArray1.length
				+ stmtArray2.length];

		System.arraycopy(stmtArray1, 0, result, 0, stmtArray1.length);
		System.arraycopy(stmtArray2, 0, result, stmtArray1.length,
				stmtArray2.length);

		return result;
	}

	/**
	 * Adds all variables defined in vl as separate VarList entries in al.
	 * Variable identifiers are extended with the given prefix.
	 * 
	 * @param al
	 *            ArrayList, where we add all variable declarations
	 * @param vl
	 *            VarList with (possibly) multiple declarations
	 * @param prefix
	 *            prefix to be added to an variable identifier
	 */
	static void addVarListToArrayList(List<VarList> al, VarList vl,
			String prefix) {
		for (final String identifier : vl.getIdentifiers()) {
			al.add(new VarList(LocationProvider.getLocation(),
					new String[] { prefix + identifier }, vl.getType()));
		}
	}

	static void addVarListToIdentifierList(List<Expression> al, VarList vl) {
		for (final String identifier : vl.getIdentifiers()) {
			al.add(new IdentifierExpression(LocationProvider.getLocation(),
					identifier));
		}
	}

	/**
	 * Returns a new Procedure with additionally specifications (for example a
	 * new "modifies")
	 * 
	 * @param p
	 * @param specs
	 * @return
	 */
	static Procedure ExtendProcedure(Procedure p, Specification[] specs) {
		final Specification[] newSpecs = new Specification[p.getSpecification().length
				+ specs.length];

		System.arraycopy(p.getSpecification(), 0, newSpecs, 0,
				p.getSpecification().length);
		System.arraycopy(specs, 0, newSpecs, p.getSpecification().length,
				specs.length);

		return new Procedure(LocationProvider.getLocation(), p.getAttributes(),
				p.getIdentifier(), p.getTypeParams(), p.getInParams(),
				p.getOutParams(), newSpecs, p.getBody());
	}
}
