package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.Collection;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml.GraphMLConverter;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.ProgramExecutionFormatter;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class CACSLProgramExecution implements IProgramExecution<CACSLLocation, IASTExpression> {

	private final ProgramState<IASTExpression> mInitialState;
	private final ArrayList<ProgramState<IASTExpression>> mProgramStates;
	private final ArrayList<AtomicTraceElement<CACSLLocation>> mTrace;

	public CACSLProgramExecution(ProgramState<IASTExpression> initialState,
			Collection<AtomicTraceElement<CACSLLocation>> trace, Collection<ProgramState<IASTExpression>> programStates) {
		assert trace != null;
		assert programStates != null;
		assert trace.size() == programStates.size();
		mProgramStates = new ArrayList<>(programStates);
		mTrace = new ArrayList<>(trace);
		mInitialState = initialState;
	}

	@Override
	public int getLength() {
		return mTrace.size();
	}

	@Override
	public AtomicTraceElement<CACSLLocation> getTraceElement(int i) {
		return mTrace.get(i);
	}

	@Override
	public ProgramState<IASTExpression> getProgramState(int i) {
		return mProgramStates.get(i);
	}

	@Override
	public ProgramState<IASTExpression> getInitialProgramState() {
		return mInitialState;
	}

	@Override
	public Class<IASTExpression> getExpressionClass() {
		return IASTExpression.class;
	}

	@Override
	public Class<CACSLLocation> getTraceElementClass() {
		return CACSLLocation.class;
	}

	@Override
	public String toString() {
		ProgramExecutionFormatter<CACSLLocation, IASTExpression> pef = new ProgramExecutionFormatter<>(
				new CACSLProgramExecutionStringProvider());
		return pef.formatProgramExecution(this);
	}

	@Override
	public String getSVCOMPWitnessString() {
		return new GraphMLConverter(this).makeGraphMLString();
	}

}
