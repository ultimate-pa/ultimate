/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
 * Result for initializer lists. E.g. for arrays and structs.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * A Result for the C to Boogie translation.
 * Stores the result of translating an initializer.
 * An initializer essentially is a nested structure of ExpressionResults.
 *
 * As a special case an initializer may contain only one ExpressionResult, for example for initializing simple type
 * variables, like ints.
 *
 * This may also represent the translation of a struct initializer or of an initializer for a (multidimensional)
 * array.
 *
 * This implementation tries to follow section 6.7.9 of the C11 standard.
 *
 * @author Markus Lindenmann
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class InitializerResult extends Result {

	/**
	 * The list holding the children elements.
	 */
	private final List<InitializerResult> list;

	/**
	 * The initializer contents for this tree node.
	 */
	private final ExpressionResult mExpressionResult;

	/**
	 * It is possible to give a struct initializer that lists the fields out of order by giving designators for each
	 * initialization value.
	 */
	private final String mDesignator;

	private List<List<Integer>> mTreeNodeIds;

	/**
	 * Constructor.
	 */
	public InitializerResult() {
		this(null);
	}

	/**
	 * Constructor.
	 *
	 * @param field
	 *            the name of the field e.g. in designated initializers.
	 */
	public InitializerResult(final String field) {
//		super(null, new LinkedHashMap<VariableDeclaration, ILocation>(0));
		super(null);
		mExpressionResult = new ExpressionResult(null, new LinkedHashMap<VariableDeclaration, ILocation>(0));
		mDesignator = field;
		list = new ArrayList<InitializerResult>();
	}

	/**
	 * Constructor.
	 *
	 * @param stmt
	 *            the statement list to hold.
	 * @param lrVal
	 *            the expression list to hold.
	 * @param decl
	 *            the declaration list to hold.
	 */
	public InitializerResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Map<VariableDeclaration, ILocation> auxVars, final List<Overapprox> overappr) {
		this(null, stmt, lrVal, decl, auxVars, overappr);
	}

	/**
	 * Constructor.
	 *
	 * @param field
	 *            the name of the field e.g. in designated initializers.
	 * @param stmt
	 *            the statement list to hold.
	 * @param lrVal
	 *            the expression list to hold.
	 * @param decl
	 *            the declaration list to hold.
	 */
	public InitializerResult(final String field, final List<Statement> stmt, final LRValue lrVal,
			final List<Declaration> decl, final Map<VariableDeclaration, ILocation> auxVars,
			final List<Overapprox> overappr) {
//		super(stmt, lrVal, decl, auxVars, overappr);
		super(null);
		mExpressionResult = new ExpressionResult(stmt, lrVal, decl, auxVars, overappr);
		this.mDesignator = field;
		list = new ArrayList<InitializerResult>();
	}

	public InitializerResult switchToRValueIfNecessary(final Dispatcher main, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final ILocation loc) {
//		final ExpressionResult re = super.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		final ExpressionResult re =
				mExpressionResult.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);

		final List<InitializerResult> newList = new ArrayList<InitializerResult>();
		if (list != null) {
			for (final InitializerResult innerRerl : list) {
				newList.add(innerRerl.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc));
			}
		}
		final InitializerResult rerl =
				new InitializerResult(mDesignator, re.stmt, re.lrVal, re.decl, re.auxVars, re.overappr);
		rerl.list.addAll(newList);
		return rerl;
	}

	public List<List<Integer>> getTreeNodeIds() {
		return mTreeNodeIds;
	}

	public ExpressionResult getTreeNode(final List<Integer> nodeId) {
		return null;
	}

	public ExpressionResult getExpressionResult() {
		return mExpressionResult;
	}

//	public LRValue getLrVal() {
//		return mExpressionResult.getLrValue();
//	}
//
//	public Collection<? extends Declaration> getDeclarations() {
//		return mExpressionResult.getDeclarations();
//	}
//
//	public Collection<? extends Statement> getStatements() {
//		return mExpressionResult.getStatements();
//	}
//
//	public Map<? extends VariableDeclaration, ? extends ILocation> getAuxVars() {
//		return mExpressionResult.getAuxVars();
//	}
//
//	public Collection<? extends Overapprox> getOverapprs() {
//		// TODO Auto-generated method stub
//		return null;
//	}

//	public Map<List<Integer>, ExpressionResult> getTree

//	public List<List<Integer>, ExpressionResult> get
}
