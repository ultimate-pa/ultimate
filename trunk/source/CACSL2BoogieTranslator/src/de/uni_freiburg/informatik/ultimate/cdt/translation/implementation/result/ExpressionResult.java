/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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
/**
 * Describing a translation result for expressions.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class ExpressionResult extends ResultWithSideEffects {
	/**
	 * the LRValue may contain the contents of a memory cell or its address or both
	 */
	private final LRValue mLrVal;

	/**
	 * We store off-heap unions as Boogie structs. When we write a field of an off-heap union, we must havoc all the
	 * other "neighbour" fields of the union. If this ExpressionResult represents a field in an off-heap union then this
	 * member contains information about the union fields that must be havocced if this union field is written.
	 */
	private final List<ExpressionResult> mOtherUnionFields;

	/**
	 * Constructor.
	 *
	 * @param stmt
	 *            the statement list to hold
	 * @param expr
	 *            the expression list to hold
	 * @param decl
	 *            the declaration list to hold
	 * @param overapproxList
	 *            list of overapproximation flags
	 */
	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Set<AuxVarInfo> auxVars, final List<Overapprox> overapproxList,
			final List<ExpressionResult> uField2CType) {
		super(null, stmt, decl, auxVars, overapproxList);
		mLrVal = lrVal;
		mOtherUnionFields = uField2CType;
	}

	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Set<AuxVarInfo> auxVars, final List<Overapprox> overapproxList) {
		this(stmt, lrVal, decl, auxVars, overapproxList, Collections.emptyList());
	}

	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Set<AuxVarInfo> auxVars) {
		this(stmt, lrVal, decl, auxVars, new ArrayList<>(), Collections.emptyList());
	}

	public ExpressionResult(final LRValue lrVal, final Set<AuxVarInfo> auxVars, final List<Overapprox> overapproxList) {
		this(new ArrayList<>(), lrVal, new ArrayList<>(), auxVars, overapproxList, Collections.emptyList());
	}

	public ExpressionResult(final List<Statement> stmt, final LRValue lrVal) {
		this(stmt, lrVal, new ArrayList<>(), new LinkedHashSet<>(), new ArrayList<>(), Collections.emptyList());
	}

	public ExpressionResult(final LRValue lrVal, final Set<AuxVarInfo> auxVars) {
		this(new ArrayList<>(), lrVal, new ArrayList<>(), auxVars);
	}

	public ExpressionResult(final LRValue lrVal) {
		this(lrVal, new LinkedHashSet<>());
	}

	public LRValue getLrValue() {
		return mLrVal;
	}

	public CType getCType() {
		return mLrVal.getCType();
	}

	public boolean hasLRValue() {
		return mLrVal != null;
	}

	public List<ExpressionResult> getNeighbourUnionFields() {
		return Collections.unmodifiableList(mOtherUnionFields);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("ExpressionResult");
		sb.append("LrVal: " + mLrVal);
		return sb.toString();
	}

	@Override
	public boolean hasNoSideEffects() {
		return super.hasNoSideEffects() && mOtherUnionFields.isEmpty();
	}
}
