/*
 * Copyright (C) 2016 Claus Schätzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Utility functions for objects from the Boogie abstract syntax tree (AST).
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public final class BoogieUtil {

	private BoogieUtil() {
		// do not instantiate utility class
	}

	/**
	 * Creates a dummy {@link IBoogieVar} from a given type. This method is used to give generated temporary variables a
	 * boogie type.
	 *
	 * @param identifier
	 *            the identifier of the variable
	 * @param type
	 *            the type of the variable
	 * @return {@link IBoogieVar} according to the given identifier and {@link IBoogieType}
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 */
	public static IBoogieVar createTemporaryIBoogieVar(final String identifier, final IBoogieType type) {
		return new TemporaryBoogieVar(type, identifier);
	}

	/**
	 * Determines if a {@link IdentifierExpression} references a variable or constant. {@link IdentifierExpression} can
	 * also reference functions or procedures. In that case, this method will return {@code false}.
	 *
	 * @param ie
	 *            {@link IdentifierExpression}
	 * @return expression references a variable or constant
	 */
	public static boolean isVariable(final IdentifierExpression ie) {
		final DeclarationInformation di = ie.getDeclarationInformation();
		switch (di.getStorageClass()) {
		case PROC_FUNC:
		case IMPLEMENTATION:
			return false;
		case GLOBAL:
		case IMPLEMENTATION_INPARAM:
		case IMPLEMENTATION_OUTPARAM:
		case LOCAL:
		case QUANTIFIED:
		case PROC_FUNC_INPARAM:
		case PROC_FUNC_OUTPARAM:
			return true;
		default:
			throw new IllegalArgumentException("Unknown storage class: " + di.getStorageClass());
		}
	}

	public static boolean isGlobal(final IBoogieVar ibv) {
		if (ibv instanceof IProgramVar) {
			return ((IProgramVar) ibv).isGlobal();
		} else if (ibv instanceof BoogieConst) {
			return true;
		} else {
			throw new AssertionError("Unknown IBoogieVar type: " + ibv.getClass().getName());
		}
	}

	public static Operator negateRelOp(final Operator relOp) {
		switch (relOp) {
		case COMPEQ:
			return Operator.COMPNEQ;
		case COMPNEQ:
			return Operator.COMPEQ;
		case COMPLEQ:
			return Operator.COMPGT;
		case COMPGT:
			return Operator.COMPLEQ;
		case COMPLT:
			return Operator.COMPGEQ;
		case COMPGEQ:
			return Operator.COMPLT;
		default:
			throw new IllegalArgumentException("Not a negatable relational operator: " + relOp);
		}
	}

}
