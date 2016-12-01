/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PathProgramVariableProvider<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
		extends RcfgVariableProvider<STATE> {
	
	public PathProgramVariableProvider(final ISymbolTableAdapter adapter, final IUltimateServiceProvider services) {
		super(new PathProgramSymbolTableAdapter(adapter), services);
	}
	
	private static class PathProgramSymbolTableAdapter implements ISymbolTableAdapter {
		
		private final ISymbolTableAdapter mAdapter;
		
		public PathProgramSymbolTableAdapter(final ISymbolTableAdapter adapter) {
			mAdapter = adapter;
		}
		
		@Override
		public Map<String, Declaration> getLocalVariables(final String procedure) {
			return mAdapter.getLocalVariables(procedure);
		}
		
		@Override
		public Set<IProgramNonOldVar> getGlobals() {
			return mAdapter.getGlobals();
		}
		
		@Override
		public Set<IProgramConst> getConsts() {
			return mAdapter.getConsts();
		}
		
		@Override
		public BoogieVar getBoogieVar(final String varId, final DeclarationInformation declarationInformation,
				final boolean inOldContext) {
			final BoogieVar rtr = mAdapter.getBoogieVar(varId, declarationInformation, inOldContext);
			return rtr;
		}
	}
	
	private static class VariableCollector {
		private final Set<CodeBlock> mPathProgram;
		
		private VariableCollector(final Set<CodeBlock> pathProgramProjection) {
			mPathProgram = pathProgramProjection;
			// mPathProgram.stream().map(a -> )
		}
	}
	
}
