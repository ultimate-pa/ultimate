package local.stalin.access;

import java.util.List;

import local.stalin.model.IElement;
import local.stalin.model.IPayload;

import org.eclipse.core.runtime.Assert;

/**
 * 
 * verschiedene Modi: 
 * 	AST /CST
 * 	global fields
 * 	global methods
 *  class signatures
 *  call dependency (startmethode angeben)
 *  
 *  general
 *  pattern matching (bestimmte Token) 
 *  pattern matching mit subgraphen
 *  pattern matching annotationen
 *  kombination 
 * 	
 * 	dynamisch / statisch 
 *  
 *  für alles 
 *  dfs / bfs 
 *  heuristik (muss funktion definieren, interface ?) 
 * 
 * @author dietsch
 *
 */

public abstract class WalkerOptions {
	
	public static enum TraversalMode {
		DFS, BFS, PRIORITY;
	}
	
	public static enum ExpansionMode{
		MATCH_TOKEN, MATCH_PAYLOAD,ALL;
	}
	
	public static enum State{
		INNER, OUTER, MARK, UNFOLD;
	}
	
	public static enum Command {
		SKIP, DESCEND, UNFOLD, MARK, INSERT_ELEMENT, REPLACE_ELEMENT, REPLACE_SUBGRAPH, REMOVE_ELEMENT, REMOVE_SUBGRAPH;
	}
	
	private final TraversalMode m_TraversalMode;
	private final ExpansionMode m_ExpansionMode;
	
	
	public WalkerOptions(TraversalMode traversalmode, ExpansionMode expansionmode) {
		Assert.isNotNull(traversalmode);
		Assert.isNotNull(expansionmode);
		m_TraversalMode = traversalmode;
		m_ExpansionMode = expansionmode;
	}
	
	public TraversalMode getTraversalMode(){
		return m_TraversalMode;
	}
	
	public ExpansionMode getExpansionMode(){
		return m_ExpansionMode;
	}

	public abstract IElement priorityFunction(List<IElement> elements);	
	
	public abstract boolean matchToken(String name);
	
	public abstract boolean matchPayload(IPayload payload);

}
