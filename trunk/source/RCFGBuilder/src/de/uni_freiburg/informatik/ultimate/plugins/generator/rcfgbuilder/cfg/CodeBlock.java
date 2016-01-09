/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

/**
 * Edge in a recursive control flow graph. A CodeBlock has a source and a target
 * which are both ProgramPoints and define how the program counter is modified
 * while executing this CodeBlock. Furthermore the subclasses of a CodeBlock
 * define how variables of the program are manipulated while executing this
 * CodeBlock. A CodeBlock is either
 * <ul>
 * <li>a sequence of Statements where each Statement is either an
 * AssumeStatement, an AssignmentStatement, or a Havoc statement.
 * <li>a sequential composition of CodeBlocks
 * <li>a parallel composition of CodeClocks.
 * </ul>
 * If the program consists of several procedures a CodeBlock can be
 * <ul>
 * <li>a Call
 * <li>a Return
 * <li>a Summary
 * </ul>
 * Furthermore a CodeBlock can be a GotoEdge, but all GotoEdges are removed when
 * the construction of the control flow graph is complete.
 * 
 * In an ULTIMATE graph a CodeBlock is an edge as well as an annotation of this
 * edge.
 * 
 * m_TransitionFormula stores a TransitionFormula that describes the effect of
 * this InternalEdge. (TODO: Add this information later, as additional
 * annotation)
 * 
 * m_OccurenceInCounterexamples is used to store in a CEGAR based verification
 * process how often this CodeBlock occurred in a counterexample. (TODO: Store
 * this information somewhere in the model checker)
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public abstract class CodeBlock extends RCFGEdge {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected final Logger mLogger;

	private final int m_Serialnumber;

	protected TransFormula m_TransitionFormula;
	protected TransFormula m_TransitionFormulaWithBranchEncoders;

	protected RCFGEdgeAnnotation m_Annotation;

	int m_OccurenceInCounterexamples = 0;

	/**
	 * Defines the maximum length of this edges name.
	 */
	private static final int MAX_NAME_LENGTH = 20;

	CodeBlock(int serialNumber, ProgramPoint source, ProgramPoint target, Logger logger) {
		super(source, target, 
				(source == null ? new Payload() : new Payload(source.getPayload().getLocation(), 
				"Matthias does not know what he should use here as a name")));
		m_Serialnumber = serialNumber;
		mLogger = logger;
		m_Annotation = new RCFGEdgeAnnotation(this) {

			private static final long serialVersionUID = 1L;

			@Override
			protected Object getFieldValue(String field) {
				return CodeBlock.this.getFieldValue(field);
			}

			@Override
			protected String[] getFieldNames() {
				return CodeBlock.this.getFieldNames();
			}
		};
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, m_Annotation);
		connectSource(source);
		connectTarget(target);
	}
	
	/**
	 * This constructor is for subclasses that are not constructed by 
	 * the CodeBlockFactory.
	 * All these CodeBlocks will have serial number "-1" and hence they will
	 * have the same hash code. 
	 */
	@Deprecated
	public CodeBlock(ProgramPoint source, ProgramPoint target, Logger logger) {
		super(source, target, 
				(source == null ? new Payload() : new Payload(source.getPayload().getLocation(), 
				"Matthias does not know what he should use here as a name")));
		m_Serialnumber = -1;
		mLogger = logger;
		m_Annotation = new RCFGEdgeAnnotation(this) {

			private static final long serialVersionUID = 1L;

			@Override
			protected Object getFieldValue(String field) {
				return CodeBlock.this.getFieldValue(field);
			}

			@Override
			protected String[] getFieldNames() {
				return CodeBlock.this.getFieldNames();
			}
		};
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, m_Annotation);
		connectSource(source);
		connectTarget(target);
	}

	/**
	 * Maybe this will be moved to subclasses.
	 */
	public void updatePayloadName() {
		String name;
		if (getPayload().hasName()) {
			name = getPayload().getName();
		} else {
			name = "";
		}
		if (name.length() < MAX_NAME_LENGTH) {
			name = getPrettyPrintedStatements();
			if (name.length() > MAX_NAME_LENGTH) {
				name = name.substring(0, MAX_NAME_LENGTH) + "...";
			}
			getPayload().setName(name);
		}
	}

	protected Object getFieldValue(String field) {
		if (field == "TransitionFormula") {
			return m_TransitionFormula;
		} else if (field == "OccurenceInCounterexamples") {
			return m_OccurenceInCounterexamples;
		} else {
			throw new UnsupportedOperationException("Unknown field " + field);
		}
	}

	protected abstract String[] getFieldNames();

	public abstract String getPrettyPrintedStatements();

	/**
	 * @return an SMT-LIB based representation of this CodeBlock's transition
	 * relation
	 */
	public TransFormula getTransitionFormula() {
		return m_TransitionFormula;
	}

	public TransFormula getTransitionFormulaWithBranchEncoders() {
		return m_TransitionFormulaWithBranchEncoders;
	}

	public void setTransitionFormula(TransFormula transFormula) {
		m_TransitionFormula = transFormula;
		m_TransitionFormulaWithBranchEncoders = transFormula;
	}

	public int getOccurenceInCounterexamples() {
		return m_OccurenceInCounterexamples;
	}

	public void reportOccurenceInCounterexample() {
		m_OccurenceInCounterexamples++;
	}

	public int getSerialNumer() {
		return m_Serialnumber;
	}

	@Override
	public int hashCode() {
		return getSerialNumer();
	}

	public final void connectSource(RCFGNode source) {
		if (source != null) {
			setSource(source);
			source.addOutgoing(this);
			// s_Logger.debug("Edge " + this + " is successor of Node " +
			// source);
		}
	}

	public final void connectTarget(RCFGNode target) {
		if (target != null) {
			setTarget(target);
			target.addIncoming(this);
			// s_Logger.debug("Node " + target + " is successor of Edge " +
			// this);
		}
	}

	/**
	 * Returns the procedure in that the system was before executing this
	 * CodeBlock. E.g., if CodeBlock is a call, the result is the name of the
	 * caller, if CodeBlock is a return the result is the callee (from which we
	 * return).
	 */
	public String getPreceedingProcedure() {
		ProgramPoint pp = (ProgramPoint) getSource();
		return pp.getProcedure();
	}

	/**
	 * Returns the procedure in that the system will be after executing the
	 * CodeBlock. E.g., if CodeBlock is a call, the result is the name of the
	 * callee, if CodeBlock is a return the result is the caller (to which we
	 * return).
	 */
	public String getSucceedingProcedure() {
		ProgramPoint pp = (ProgramPoint) getTarget();
		return pp.getProcedure();
	}

	@Override
	public abstract String toString();

}
