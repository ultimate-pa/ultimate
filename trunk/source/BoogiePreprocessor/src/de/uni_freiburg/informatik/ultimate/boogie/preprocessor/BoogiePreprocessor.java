package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.boogie.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTableConstructor;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;

/**
 * This class initializes the boogie preprocessor.
 * 
 * @author hoenicke
 * 
 */
public class BoogiePreprocessor implements IAnalysis {

    private static final String s_PLUGIN_NAME = "Boogie Preprocessor";
    private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;

    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init() {
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


    public GraphType getOutputDefinition() {
        /* use old graph type definition */
        return null;
    }

    public void setInputDefinition(GraphType graphType) {
        // not required.
    }

    // @Override
    public List<IObserver> getObservers() {
        ArrayList<IObserver> observers = new ArrayList<IObserver>();
        observers.add(new TypeChecker());
        observers.add(new ConstExpander());
        observers.add(new StructExpander());
        observers.add(new UnstructureCode());
        observers.add(new FunctionInliner());
        observers.add(new BoogieSymbolTableConstructor());
        return observers;
    }

    @Override
    public boolean isGuiRequired() {
        return false;
    }


    /**
     * Add all annotation from annot to node. annot should not be null.
     * 
     * @param from node to take annotations from
     * @param to node to add annotations to
     * @author Christian & Matthias
     */
    public static void passAnnotations(BoogieASTNode from, BoogieASTNode to) {
        if (from.getPayload().hasAnnotation()) {
            to.getPayload().getAnnotations().putAll(
                    from.getPayload().getAnnotations());
        }
    }

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}
}
