package local.stalin.boogie.preprocessor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IAnalysis;
import local.stalin.model.GraphType;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

/**
 * This class initializes the boogie preprocessor.
 * 
 * @author hoenicke
 *
 */
public class BoogiePreprocessor implements IAnalysis {

	private static final String s_PLUGIN_NAME = "Boogie Preprocessor";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	
	private TypeChecker m_typechecker;
	private List<MarkedTrace> m_MarkedTraces;
	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
    	m_typechecker = new TypeChecker();
    	return -1;
    }

	/**
	 * I give you every model.
	 */
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	/**
	 * I don't need a special tool
	 */
	public List<String> getDesiredToolID() {
		return null;
	}

	/**
	 * I don't use the TokenMap right now.
	 */
	public void setTokenMap(TokenMap tokenMap) {
	}

	public GraphType getOutputDefinition() {
		/* use old graph type definition */
		return null;
	}

	public void setInputDefinition(GraphType graphType) {
	}

	//@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(m_typechecker);
		observers.add(new UnstructureCode());
		observers.add(new FunctionInliner());
		observers.add(new ConstExpander());
		return observers;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public List<MarkedTrace> getMarkedTraces() {
		// TODO implement traces 
		return m_MarkedTraces;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}



}
