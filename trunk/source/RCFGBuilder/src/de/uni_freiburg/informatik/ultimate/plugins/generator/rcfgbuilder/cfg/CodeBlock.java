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

import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Edge in a recursive control flow graph. A CodeBlock has a source and a target which are both ProgramPoints and define
 * how the program counter is modified while executing this CodeBlock. Furthermore the subclasses of a CodeBlock define
 * how variables of the program are manipulated while executing this CodeBlock. A CodeBlock is either
 * <ul>
 * <li>a sequence of Statements where each Statement is either an AssumeStatement, an AssignmentStatement, or a Havoc
 * statement.
 * <li>a sequential composition of CodeBlocks
 * <li>a parallel composition of CodeClocks.
 * </ul>
 * If the program consists of several procedures a CodeBlock can be
 * <ul>
 * <li>a Call
 * <li>a Return
 * <li>a Summary
 * </ul>
 * Furthermore a CodeBlock can be a GotoEdge, but all GotoEdges are removed when the construction of the control flow
 * graph is complete.
 *
 * In an ULTIMATE graph a CodeBlock is an edge as well as an annotation of this edge.
 *
 * mTransitionFormula stores a TransitionFormula that describes the effect of this InternalEdge. (TODO: Add this
 * information later, as additional annotation)
 *
 * mOccurenceInCounterexamples is used to store in a CEGAR based verification process how often this CodeBlock occurred
 * in a counterexample. (TODO: Store this information somewhere in the model checker)
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class CodeBlock extends IcfgEdge {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected final ILogger mLogger;

	private final int mSerialnumber;

	protected UnmodifiableTransFormula mTransitionFormula;
	protected UnmodifiableTransFormula mTransitionFormulaWithBranchEncoders;

	private String mPrecedingProcedure;
	private String mSucceedingProcedure;

	protected RCFGEdgeAnnotation mAnnotation;

	private int mOccurenceInCounterexamples = 0;

	CodeBlock(final int serialNumber, final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final ILogger logger) {
		super(source, target, source == null ? new Payload() : new Payload(source.getPayload()));
		mSerialnumber = serialNumber;
		mLogger = logger;
		connectSource(source);
		connectTarget(target);
		setPreceedingProcedure(source);
		setSucceedingProcedure(target);
	}

	/**
	 * This constructor is for subclasses that are not constructed by the CodeBlockFactory. All these CodeBlocks will
	 * have serial number "-1" and hence they will have the same hash code.
	 *
	 * @deprecated Do not use this constructor, use the {@link CodeBlockFactory} instead.
	 */
	@Deprecated
	public CodeBlock(final BoogieIcfgLocation source, final BoogieIcfgLocation target, final ILogger logger) {
		super(source, target, source == null ? new Payload() : new Payload(source.getPayload()));
		mSerialnumber = -1;
		mLogger = logger;
		connectSource(source);
		connectTarget(target);
	}

	@Visualizable
	public abstract String getPrettyPrintedStatements();

	/**
	 * @return an SMT-LIB based representation of this CodeBlock's transition relation
	 */
	@Override
	@Visualizable
	public UnmodifiableTransFormula getTransformula() {
		return mTransitionFormula;
	}

	public UnmodifiableTransFormula getTransitionFormulaWithBranchEncoders() {
		return mTransitionFormulaWithBranchEncoders;
	}

	public void setTransitionFormula(final UnmodifiableTransFormula transFormula) {
		mTransitionFormula = transFormula;
		mTransitionFormulaWithBranchEncoders = transFormula;
	}

	@Visualizable
	public int getOccurenceInCounterexamples() {
		return mOccurenceInCounterexamples;
	}

	public void reportOccurenceInCounterexample() {
		mOccurenceInCounterexamples++;
	}

	public int getSerialNumber() {
		return mSerialnumber;
	}

	private void setPreceedingProcedure(final IcfgLocation source) {
		if (source instanceof BoogieIcfgLocation) {
			final String name = ((BoogieIcfgLocation) source).getProcedure();
			if (mPrecedingProcedure == null) {
				mPrecedingProcedure = name;
			} else {
				if (mPrecedingProcedure.equals(name)) {
					// do nothing
				} else {
					throw new AssertionError("proc must not change");
				}
			}
		}
	}

	private void setSucceedingProcedure(final IcfgLocation source) {
		if (source instanceof BoogieIcfgLocation) {
			final String name = ((BoogieIcfgLocation) source).getProcedure();
			if (mSucceedingProcedure == null) {
				mSucceedingProcedure = name;
			} else {
				if (mSucceedingProcedure.equals(name)) {
					// do nothing
				} else {
					throw new AssertionError("proc must not change");
				}
			}
		}
	}

	public final void connectSource(final IcfgLocation source) {
		if (source != null) {
			setSource(source);
			source.addOutgoing(this);
		}
	}

	public final void connectTarget(final IcfgLocation target) {
		if (target != null) {
			setTarget(target);
			target.addIncoming(this);
		}
	}

	/**
	 * Returns the procedure in that the system was before executing this CodeBlock. E.g., if CodeBlock is a call, the
	 * result is the name of the caller, if CodeBlock is a return the result is the callee (from which we return).
	 */
	@Override
	public String getPrecedingProcedure() {
		if (mPrecedingProcedure == null) {
			throw new IllegalArgumentException("Preceding procedure has not yet been determined.");
		}
		return mPrecedingProcedure;
	}

	/**
	 * Returns the procedure in that the system will be after executing the CodeBlock. E.g., if CodeBlock is a call, the
	 * result is the name of the callee, if CodeBlock is a return the result is the caller (to which we return).
	 */
	@Override
	public String getSucceedingProcedure() {
		if (mSucceedingProcedure == null) {
			throw new IllegalArgumentException("Succeeding procedure has not yet been determined.");
		}
		return mSucceedingProcedure;
	}

	@Override
	public abstract String toString();

	@Override
	public void setTarget(final IcfgLocation target) {
		setSucceedingProcedure(target);
		super.setTarget(target);
	}

	@Override
	public void setSource(final IcfgLocation source) {
		setPreceedingProcedure(source);
		super.setSource(source);
	}

	/**
	 * @return the number of open calls contained in this codeblock.
	 */
	protected int getNumberOfOpenCalls() {
		return 0;
	}

	@Override
	public final int hashCode() {
		return getSerialNumber();
	}
}
