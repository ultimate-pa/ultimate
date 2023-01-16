/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;

/**
 * A super-class for results that may have side effects, i.e., it contains statements, variable declaration or auxiliary
 * variables; and it may have overapproximation flags.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public abstract class ResultWithSideEffects extends Result {
	/**
	 * Statement list.
	 */
	private final List<Statement> mStmt;

	/**
	 * Declaration list. Some translations need to declare some temporary variables, which we do here.
	 */
	// FIXME: could we also use the more special type VariableDeclaration here??
	private final List<Declaration> mDecl;

	/**
	 * Auxiliary variables occurring in this result. The variable declaration of the var is mapped to the exact location
	 * for that it was constructed.
	 */
	private final Set<AuxVarInfo> mAuxVars;

	/**
	 * A list of overapproximation flags.
	 */
	private final List<Overapprox> mOverappr;

	public ResultWithSideEffects(final BoogieASTNode node, final List<Statement> stmt, final List<Declaration> decl,
			final Set<AuxVarInfo> auxVars, final List<Overapprox> overapproxList) {
		super(node);
		mStmt = stmt;
		mDecl = decl;
		mAuxVars = auxVars;
		mOverappr = overapproxList;
	}

	public List<Statement> getStatements() {
		return Collections.unmodifiableList(mStmt);
	}

	public List<Declaration> getDeclarations() {
		return Collections.unmodifiableList(mDecl);
	}

	public Set<AuxVarInfo> getAuxVars() {
		return Collections.unmodifiableSet(mAuxVars);
	}

	public List<Overapprox> getOverapprs() {
		return Collections.unmodifiableList(mOverappr);
	}

	/**
	 * Returns true if this result has no actual side effects
	 *
	 * @return
	 */
	public boolean hasNoSideEffects() {
		if (!mStmt.isEmpty()) {
			return false;
		}
		if (!mDecl.isEmpty()) {
			return false;
		}
		if (!mAuxVars.isEmpty()) {
			return false;
		}
		if (!mOverappr.isEmpty()) {
			return false;
		}
		return true;
	}
}
