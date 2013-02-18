package de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;

public abstract class IErrorTrace extends ArrayList<Statement> {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2491619769649163147L;
	
	private Script mScript = null;
	
	protected IErrorTrace(Script script) {
		mScript = script;
	}
	
	protected abstract void process();
	
	public ArrayList<ILocation> getLocations() {
		ArrayList<ILocation> result = new ArrayList<ILocation>();
		for(Statement statement: this) {
			result.add(statement.getLocation());
		}
		return result;
	}
	
	public Script getScript() {
		return mScript;
	}
	
	public ILocation getErrorLocation() {
		return this.get(this.size()-1).getLocation();
	}

	public abstract ArrayList<IElement> getErrorPath();
	
	public abstract Term[] getFormulas();
	
	public abstract IElement getGraphroot();
	
	public abstract Procedure getProcedure();
	
	public IResult getCounterExampleResult() {
		ArrayList<ILocation> locationsOfAllTakenTransitions = new ArrayList<ILocation>();
		locationsOfAllTakenTransitions = this.getLocations();

		CounterExampleResult counterExampleResult = new CounterExampleResult(null,
				Activator.s_PLUGIN_NAME,
				UltimateServices.getInstance().getTranslatorSequence(),				
				locationsOfAllTakenTransitions.isEmpty()?null:
			locationsOfAllTakenTransitions.get(
					locationsOfAllTakenTransitions.size()-1), null);  //TODO valuation
		
		counterExampleResult.setFailurePath(locationsOfAllTakenTransitions);
		counterExampleResult.setShortDescription("Program is unsafe!");
		counterExampleResult.setLongDescription(getErrorPath().toString() + " is a real counterexample! " +
				"The actual error trace is " + locationsOfAllTakenTransitions);
		return counterExampleResult;
	}

}

