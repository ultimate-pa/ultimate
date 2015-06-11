package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Deque;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class AbstractInterpreter<T extends IElement> {

	private final IPost<T> mPost;
	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	public AbstractInterpreter(IUltimateServiceProvider services, IPost<T> post) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPost = post;
	}

	public void process(T elem) {
		Deque<T> worklist = new ArrayDeque<T>();
		worklist.add(elem);
		
		while(!worklist.isEmpty()){
			final T current = worklist.removeFirst();
			
		}
		
	}

}
