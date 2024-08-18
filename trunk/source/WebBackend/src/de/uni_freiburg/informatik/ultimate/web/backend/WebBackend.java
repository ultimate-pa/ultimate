package de.uni_freiburg.informatik.ultimate.web.backend;

import java.nio.file.Path;
import java.util.EnumSet;

import javax.servlet.DispatcherType;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.handler.ContextHandlerCollection;
import org.eclipse.jetty.ee8.nested.ContextHandler;
import org.eclipse.jetty.ee8.nested.ResourceHandler;
import org.eclipse.jetty.ee8.servlet.FilterHolder;
import org.eclipse.jetty.ee8.servlet.ServletContextHandler;
import org.eclipse.jetty.ee8.servlet.ServletHolder;
import org.eclipse.jetty.util.resource.PathResourceFactory;
import org.eclipse.jetty.util.resource.Resource;

import de.uni_freiburg.informatik.ultimate.web.backend.util.CrossOriginFilter;

public class WebBackend implements IApplication {

	private static final Logger LOGGER = LogManager.getLogger();
	
	private Server mJettyServer;

	public WebBackend() {
		// no init necessary
	}

	@Override
	public Object start(final IApplicationContext context) throws Exception {
		System.setProperty("org.eclipse.jetty.util.log.class", "org.eclipse.jetty.util.log.LoggerLog");

		Config.load();

		initJettyServer();

		mJettyServer.start();
		mJettyServer.join();

		return EXIT_OK;
	}

	@Override
	public void stop() {
		try {
			mJettyServer.stop();
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Initialize Jetty front- and back-end server.
	 */
	private void initJettyServer() {
		mJettyServer = new Server(Config.PORT);
		final ContextHandlerCollection contexts = new ContextHandlerCollection();
		mJettyServer.setHandler(contexts);

		// Serve the website (front-end) as static content.
		if (Config.SERVE_WEBSITE) {
			final Path absPath = Config.tryGetAbsolutePath(Config.FRONTEND_PATH);
			addStaticPathToContext(contexts, absPath, Config.FRONTEND_ROUTE);
			LOGGER.info("Serving frontend (" + absPath.toString() + ") at route: " + Config.FRONTEND_ROUTE);
		}

		// Serve the API.
		// Prepare Handler for API servlets.
		final ServletContextHandler servlets = new ServletContextHandler(contexts, "/", ServletContextHandler.SESSIONS);
		// Add the API servlet.
		servlets.addServlet(new ServletHolder(new UltimateApiServlet()), Config.BACKEND_ROUTE + "/*");

		// Enable CORS to allow ultimate back-end/front-end running on a separate port and domain.
		enableCorsOnServletContextHandler(servlets);

		LOGGER.info("Serving API at route: " + Config.BACKEND_ROUTE);
	}

	/**
	 * Serve files in folderPath static at the routePath.
	 *
	 * @param contextCollection
	 * @param folderPath
	 *            Path to the static files to be served.
	 * @param routePath
	 *            The route the files should be served at (e.g. "/media").
	 */
	private static void addStaticPathToContext(final ContextHandlerCollection contextCollection, final Path folderPath,
			final String routePath) {
		final ResourceHandler frontendResourceHandler = new ResourceHandler();
		frontendResourceHandler.setDirAllowed(true);

		final PathResourceFactory resourceFactory = new PathResourceFactory();
		final Resource folderPathRes = resourceFactory.newResource(folderPath.toUri());

		final ContextHandler frontendContextHandler = new ContextHandler();
		frontendContextHandler.setContextPath(routePath);
		frontendContextHandler.setBaseResource(folderPathRes);
		frontendContextHandler.setHandler(frontendResourceHandler);

		contextCollection.addHandler(frontendContextHandler);
	}

	/**
	 * Add CORS headers to the servlets in the servlet handler. Enables the servlets to be called from outside their
	 * served domain.
	 *
	 * @param contexts
	 *            ServletContextHandler
	 */
	private static void enableCorsOnServletContextHandler(final ServletContextHandler contexts) {
		final FilterHolder cors = new FilterHolder(new CrossOriginFilter());
		contexts.addFilter(cors, "/*", EnumSet.of(DispatcherType.REQUEST));

		cors.setInitParameter(CrossOriginFilter.ALLOWED_ORIGINS_PARAM, "*");
		cors.setInitParameter(CrossOriginFilter.ACCESS_CONTROL_ALLOW_ORIGIN_HEADER, "*");
		cors.setInitParameter(CrossOriginFilter.ALLOWED_METHODS_PARAM, "GET,POST");

	}
}
