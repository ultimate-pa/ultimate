/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.optimizeproduct;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.TransFormulaAdder;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RcfgEdgeBuilder {
	
	private final TransFormulaAdder mTransForumlaAdder;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;
	private final CodeBlockFactory mCbf;
	
	public RcfgEdgeBuilder(final BoogieIcfgContainer icfg, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mTransForumlaAdder = new TransFormulaAdder(icfg.getBoogie2SMT(), services);
		mCbf = icfg.getCodeBlockFactory();
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
	}
	
	private void addTransFormula(final StatementSequence ss) {
		addTransFormula(ss, ss.getPrecedingProcedure());
	}
	
	private void addTransFormula(final CodeBlock cb, final String procId) {
		mTransForumlaAdder.addTransitionFormulas(cb, procId, mXnfConversionTechnique, mSimplificationTechnique);
	}
	
	public SequentialComposition constructSequentialComposition(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final CodeBlock first, final CodeBlock second) {
		final SequentialComposition sc = mCbf.constructSequentialComposition(source, target, false, false,
				Arrays.asList(new CodeBlock[] { first, second }), mXnfConversionTechnique, mSimplificationTechnique);
		assert sc.getTransformula() != null : "Transformula was not added although it should have been";
		assert sc.getTransitionFormula() != null;
		assert sc.getTarget() != null;
		assert sc.getSource() != null;
		return sc;
	}
	
	public StatementSequence constructStatementSequence(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final List<Statement> statements) {
		final StatementSequence ss = mCbf.constructStatementSequence(source, target, statements, Origin.IMPLEMENTATION);
		addTransFormula(ss);
		assert ss.getTransformula() != null : "Transformula was not added although it should have been";
		assert ss.getTransitionFormula() != null;
		return ss;
	}
	
	public StatementSequence constructStatementSequence(final BoogieIcfgLocation source,
			final BoogieIcfgLocation target, final Statement stmt) {
		return constructStatementSequence(source, target, Collections.singletonList(stmt));
	}
}
