package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.models.ISimpleAST;
import de.uni_freiburg.informatik.ultimate.model.IElementTest;

/**
 * TODO: The class, that shall be tested here, implements three different Interfaces. Multiple inheritance is not
 * supported by Java, so this must somehow be solved another way.
 * 
 * @author Jeremi Dzienian
 *
 * @param <T>
 */
public abstract class ISimpleASTTest<T extends ISimpleAST<?, ?>> extends IElementTest<T> {

	@Test
	public void getOutgoingNodesNotNull() {
		final List<?> ret = instance.getOutgoingNodes();

		Assert.assertNotNull(ret);
	}

}
