/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.model.IStorable;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

/**
 * Factory for the construction of CodeBlocks.
 * Every CodeBlock has to be constructed via this factory, because
 * every CodeBlock need a unique serial number.
 * Every control flow graph has to provide one CodeBlockFactory
 * 
 * @author Matthias Heizmann
 *
 */
public class CodeBlockFactory implements IStorable {
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	private final Boogie2SMT m_Boogie2smt;
	private final ModifiableGlobalVariableManager m_MgvManager;
	
	public final static String s_CodeBlockFactoryKeyInToolchainStorage = "CodeBlockFactory";
	
	private int m_SerialNumberCounter = 0;	
	
	public CodeBlockFactory(IUltimateServiceProvider services,
			Boogie2SMT boogie2smt, ModifiableGlobalVariableManager mgvManager) {
		super();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		m_Boogie2smt = boogie2smt;
		m_MgvManager = mgvManager;
	}
	
	public Call constructCall(ProgramPoint source, ProgramPoint target, 
			CallStatement call) {
		return new Call(m_SerialNumberCounter++, source, target, call, m_Logger);
	}
	
	public InterproceduralSequentialComposition constuctInterproceduralSequentialComposition(ProgramPoint source, ProgramPoint target, 
			boolean simplify, boolean extPqe, List<CodeBlock> codeBlocks) {
		return new InterproceduralSequentialComposition(m_SerialNumberCounter++, source, target, 
				m_Boogie2smt, m_MgvManager, simplify, extPqe, codeBlocks, m_Logger, m_Services);
	}
	
	public GotoEdge constructGotoEdge(ProgramPoint source, ProgramPoint target) {
		return new GotoEdge(m_SerialNumberCounter++, source, target, m_Logger);
	}
	
	public ParallelComposition constructParallelComposition(ProgramPoint source, ProgramPoint target, 
			List<CodeBlock> codeBlocks) {
		return new ParallelComposition(m_SerialNumberCounter++, source, target, 
				m_Boogie2smt, m_Services, codeBlocks);
	}
	
	public Return constructReturn(
			ProgramPoint source, ProgramPoint target, Call correspondingCall) {
		return new Return(m_SerialNumberCounter++, source, target, 
				correspondingCall, m_Logger);
	}

	public SequentialComposition constructSequentialComposition(ProgramPoint source, ProgramPoint target, 
			boolean simplify, boolean extPqe, List<CodeBlock> codeBlocks) {
		return new SequentialComposition(m_SerialNumberCounter++, source, target, 
				m_Boogie2smt, m_MgvManager, simplify, extPqe, m_Services, codeBlocks);
	}
	
	public StatementSequence constructStatementSequence(ProgramPoint source, ProgramPoint target, 
			Statement st) {
		return new StatementSequence(m_SerialNumberCounter++, source, target, 
				st, m_Logger);
	}
	
	public StatementSequence constructStatementSequence(ProgramPoint source, ProgramPoint target, 
			Statement st, Origin origin) {
		return new StatementSequence(m_SerialNumberCounter++, source, target, 
				st, origin, m_Logger);
	}
	
	public StatementSequence constructStatementSequence(ProgramPoint source, ProgramPoint target, 
			List<Statement> stmts, Origin origin) {
		return new StatementSequence(m_SerialNumberCounter++, source, target, 
				stmts, origin, m_Logger);
	}
	
	public Summary constructSummary(ProgramPoint source, ProgramPoint target, 
			CallStatement st, boolean calledProcedureHasImplementation) {
		return new Summary(m_SerialNumberCounter++, source, target, 
				st, calledProcedureHasImplementation, m_Logger);
	}
	
	
	
	
	public CodeBlock copyCodeBlock(CodeBlock codeBlock, ProgramPoint source, ProgramPoint target) {
		if (codeBlock instanceof Call) {
			Call copy = this.constructCall(source, target, ((Call) codeBlock).getCallStatement());
			copy.setTransitionFormula(codeBlock.getTransitionFormula());
			return copy;
		} else if (codeBlock instanceof Return) {
			Return copy = this.constructReturn(source, target, ((Return) codeBlock).getCorrespondingCall());
			copy.setTransitionFormula(codeBlock.getTransitionFormula());
			return copy;
		} else if (codeBlock instanceof StatementSequence) {
			List<Statement> statements = ((StatementSequence) codeBlock).getStatements();
			Origin origin = ((StatementSequence) codeBlock).getOrigin();
			StatementSequence copy = this.constructStatementSequence(source, target, statements, origin);
			copy.setTransitionFormula(codeBlock.getTransitionFormula());
			return copy;
		} else if (codeBlock instanceof Summary) {
			CallStatement callStatement = ((Summary) codeBlock).getCallStatement();
			boolean calledProcedureHasImplementation = ((Summary) codeBlock).calledProcedureHasImplementation();
			Summary copy = this.constructSummary(source, target, callStatement, calledProcedureHasImplementation);
			copy.setTransitionFormula(codeBlock.getTransitionFormula());
			return copy;
		} else if (codeBlock instanceof GotoEdge) {
			GotoEdge copy = this.constructGotoEdge(source, target);
			return copy;
		} else {
			throw new UnsupportedOperationException("unsupported kind of CodeBlock");
		}
	}




	@Override
	public void destroy() {
		// nothing to destroy
	}

}
