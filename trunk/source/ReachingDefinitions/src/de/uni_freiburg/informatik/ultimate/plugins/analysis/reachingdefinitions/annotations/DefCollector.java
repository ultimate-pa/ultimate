/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

class DefCollector extends RCFGEdgeVisitor {

	private HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> mDefs;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mAnnotationProvider;
	private final String mKey;

	DefCollector(final IAnnotationProvider<ReachDefStatementAnnotation> provider, final String key) {
		mAnnotationProvider = provider;
		mKey = key;
	}

	HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> collect(final IcfgEdge edge) {
		if (mDefs == null) {
			mDefs = new HashMap<>();
			visit(edge);
		}
		return mDefs;
	}

	@Override
	protected void visit(final SequentialComposition c) {
		final List<CodeBlock> blck = c.getCodeBlocks();
		if (blck == null || blck.isEmpty()) {
			return;
		}
		super.visit(blck.get(blck.size() - 1));
	}

	@Override
	protected void visit(final StatementSequence c) {
		super.visit(c);

		final List<Statement> stmts = c.getStatements();

		if (stmts == null || stmts.isEmpty()) {
			return;
		}

		final ReachDefBaseAnnotation annot = getAnnotation(stmts);
		if (annot != null) {
			mDefs = annot.getDefs();
		}
	}

	private ReachDefBaseAnnotation getAnnotation(final List<Statement> stmts) {
		if (mKey == null) {
			return mAnnotationProvider.getAnnotation(stmts.get(stmts.size() - 1));
		}
		return mAnnotationProvider.getAnnotation(stmts.get(stmts.size() - 1), mKey);
	}

}
