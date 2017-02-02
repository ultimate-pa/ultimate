package de.uni_freiburg.informatik.ultimate.webinterface;

import org.osgi.framework.BundleContext;
import org.osgi.framework.ServiceReference;
import org.osgi.service.http.HttpService;
import org.osgi.util.tracker.ServiceTracker;

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

	@Override
	public HttpService addingService(ServiceReference<Object> reference) {
		final HttpService http = (HttpService) context.getService(reference);
		try {
			http.registerServlet("/if", new UltimateHttpServlet(), null, null);
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return http;
	}

	@Override
	public void removedService(ServiceReference<Object> reference,
			HttpService service) {
		final HttpService http = service;
		http.unregister("/if");
		super.removedService(reference, service);
	}

	@Override
	public void modifiedService(ServiceReference<Object> reference,
			HttpService service) {
		super.modifiedService(reference, service);
	}
}
