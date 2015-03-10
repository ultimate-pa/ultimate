package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Observer that stores the root node of a model if this node has a given type.
 * @author Matthias Heizmann
 *
 * @param <E> Type of the root node that will be stored.
 */
public class RootNodeFilterObserver<E extends IElement> implements IUnmanagedObserver {
	private final Class<E> m_RootNodeClass;
	private E m_RootNode = null;
	
	public RootNodeFilterObserver(Class<E> rootNodeClass) {
		super();
		m_RootNodeClass = rootNodeClass;
	}
	
	public E getRootNode() {
		return m_RootNode;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex,
			int numberOfModels) throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (m_RootNodeClass.isAssignableFrom(root.getClass())) {
			if (m_RootNode == null) {
				m_RootNode = (E) root;
			} else {
				throw new IllegalStateException("root node of type " + 
						m_RootNodeClass.getSimpleName()  + " was already found");
			}
		}
		return false;
	}

}
