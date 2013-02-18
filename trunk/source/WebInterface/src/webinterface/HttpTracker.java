package webinterface;

import org.osgi.framework.BundleContext;
import org.osgi.framework.ServiceReference;
import org.osgi.service.http.HttpService;
import org.osgi.util.tracker.ServiceTracker;

import de.uni_freiburg.informatik.ultimate.website.UltimateInterface;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 25.03.2012
 */
public class HttpTracker extends ServiceTracker<Object, HttpService> {

	/**
	 * Constructor: Calls the super constructor.
	 * 
	 * @param context
	 *            the bundle context.
	 */
	HttpTracker(BundleContext context) {
		super(context, HttpService.class.getName(), null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.osgi.util.tracker.ServiceTracker#addingService(org.osgi.framework
	 * .ServiceReference)
	 */
	@Override
	public HttpService addingService(ServiceReference<Object> reference) {
		final HttpService http = (HttpService) context.getService(reference);
		try {
			http.registerServlet("/if", new UltimateInterface(), null, null);
		} catch (Exception e) {
			e.printStackTrace();
		}
		return http;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.osgi.util.tracker.ServiceTracker#removedService(org.osgi.framework
	 * .ServiceReference, java.lang.Object)
	 */
	@Override
	public void removedService(ServiceReference<Object> reference,
			HttpService service) {
		final HttpService http = (HttpService) service;
		http.unregister("/if");
		super.removedService(reference, service);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.osgi.util.tracker.ServiceTracker#modifiedService(org.osgi.framework
	 * .ServiceReference, java.lang.Object)
	 */
	@Override
	public void modifiedService(ServiceReference<Object> reference,
			HttpService service) {
		super.modifiedService(reference, service);
	}
}
