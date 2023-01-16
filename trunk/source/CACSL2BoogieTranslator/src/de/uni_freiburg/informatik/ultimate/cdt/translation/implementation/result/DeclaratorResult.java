/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;

/**
 * A Result that contain one CDeclaration. It should be used when a declarator is dispatched. .. or more general:
 * whenever we have something declaration-like where we know that only one symbol is declared/one type is involved --> a
 * typeIdExpression is such a case, a SimpleDeclaration is not, for example.
 */
public class DeclaratorResult extends ResultWithSideEffects {

	CDeclaration mDecl;

	public DeclaratorResult(final CDeclaration cd) {
		this(cd, Collections.emptyList(), Collections.emptyList(), Collections.emptySet(), Collections.emptyList());
	}

	public DeclaratorResult(final CDeclaration cd, final ResultWithSideEffects sideEffects) {
		this(cd, sideEffects.getStatements(), sideEffects.getDeclarations(), sideEffects.getAuxVars(),
				sideEffects.getOverapprs());
	}

	public DeclaratorResult(final CDeclaration cd, final List<Statement> stmt, final List<Declaration> decl,
			final Set<AuxVarInfo> auxVars, final List<Overapprox> overapproxList) {
		super(null, stmt, decl, auxVars, overapproxList);
		mDecl = cd;
	}

	public CDeclaration getDeclaration() {
		return mDecl;
	}

	@Override
	public String toString() {
		return mDecl.toString();
	}
}
