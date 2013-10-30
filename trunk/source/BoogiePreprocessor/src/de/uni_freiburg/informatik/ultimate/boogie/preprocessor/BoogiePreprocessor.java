package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;

/**
 * This class initializes the boogie preprocessor.
 * 
 * @author hoenicke
 * 
 */
public class BoogiePreprocessor implements IAnalysis {

    private static final String s_PLUGIN_NAME = "Boogie Preprocessor";
    private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
    private List<MarkedTrace> m_MarkedTraces;

    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
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
        // not required.
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
    public IEclipsePreferences[] getPreferences(IScopeContext cs,
            IScopeContext is) {
        return new IEclipsePreferences[] { cs.getNode(s_PLUGIN_ID) };
    }

    /**
     * Add all annotation from annot to node. annot should not be null.
     * 
     * @param from node to take annotations from
     * @param to node to add annotations to
     * @author Christian & Matthias
     */
    public static void passAnnotations(ASTNode from, ASTNode to) {
        if (from.getPayload().hasAnnotation()) {
            to.getPayload().getAnnotations().putAll(
                    from.getPayload().getAnnotations());
        }
    }
}
