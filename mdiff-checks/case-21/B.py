# coding: utf-8
"""Constants used by Home Assistant components."""
MAJOR_VERSION = 0
MINOR_VERSION = 43
PATCH_VERSION = '1'
__short_version__ = '{}.{}'.format(MAJOR_VERSION, MINOR_VERSION)
__version__ = '{}.{}'.format(__short_version__, PATCH_VERSION)
REQUIRED_PYTHON_VER = (3, 4, 2)
REQUIRED_PYTHON_VER_WIN = (3, 5, 2)
CONSTRAINT_FILE = 'package_constraints.txt'

PROJECT_NAME = 'Home Assistant'
PROJECT_PACKAGE_NAME = 'homeassistant'
PROJECT_LICENSE = 'Apache License 2.0'
PROJECT_AUTHOR = 'The Home Assistant Authors'
PROJECT_COPYRIGHT = ' 2013, {}'.format(PROJECT_AUTHOR)
PROJECT_URL = 'https://home-assistant.io/'
PROJECT_EMAIL = 'hello@home-assistant.io'
PROJECT_DESCRIPTION = ('Open-source home automation platform '
                       'running on Python 3.')
PROJECT_LONG_DESCRIPTION = ('Home Assistant is an open-source '
                            'home automation platform running on Python 3. '
                            'Track and control all devices at home and '
                            'automate control. '
                            'Installation in less than a minute.')
PROJECT_CLASSIFIERS = [
    'Intended Audience :: End Users/Desktop',
    'Intended Audience :: Developers',
    'License :: OSI Approved :: Apache Software License',
    'Operating System :: OS Independent',
    'Programming Language :: Python :: 3.4',
    'Topic :: Home Automation'
]

PROJECT_GITHUB_USERNAME = 'home-assistant'
PROJECT_GITHUB_REPOSITORY = 'home-assistant'

PYPI_URL = 'https://pypi.python.org/pypi/{}'.format(PROJECT_PACKAGE_NAME)
GITHUB_PATH = '{}/{}'.format(PROJECT_GITHUB_USERNAME,
                             PROJECT_GITHUB_REPOSITORY)
GITHUB_URL = 'https://github.com/{}'.format(GITHUB_PATH)

PLATFORM_FORMAT = '{}.{}'

# Can be used to specify a catch all when registering state or event listeners.
MATCH_ALL = '*'

# If no name is specified
DEVICE_DEFAULT_NAME = 'Unnamed Device'

WEEKDAYS = ['mon', 'tue', 'wed', 'thu', 'fri', 'sat', 'sun']

SUN_EVENT_SUNSET = 'sunset'
SUN_EVENT_SUNRISE = 'sunrise'

# #### CONFIG ####
CONF_ABOVE = 'above'
CONF_ACCESS_TOKEN = 'access_token'
CONF_AFTER = 'after'
CONF_ALIAS = 'alias'
CONF_API_KEY = 'api_key'
CONF_AUTHENTICATION = 'authentication'
CONF_BASE = 'base'
CONF_BEFORE = 'before'
CONF_BELOW = 'below'
CONF_BINARY_SENSORS = 'binary_sensors'
CONF_BLACKLIST = 'blacklist'
CONF_BRIGHTNESS = 'brightness'
CONF_CODE = 'code'
CONF_COLOR_TEMP = 'color_temp'
CONF_COMMAND = 'command'
CONF_COMMAND_CLOSE = 'command_close'
CONF_COMMAND_OFF = 'command_off'
CONF_COMMAND_ON = 'command_on'
CONF_COMMAND_OPEN = 'command_open'
CONF_COMMAND_STATE = 'command_state'
CONF_COMMAND_STOP = 'command_stop'
CONF_CONDITION = 'condition'
CONF_COVERS = 'covers'
CONF_CUSTOMIZE = 'customize'
CONF_CUSTOMIZE_DOMAIN = 'customize_domain'
CONF_CUSTOMIZE_GLOB = 'customize_glob'
CONF_DEVICE = 'device'
CONF_DEVICE_CLASS = 'device_class'
CONF_DEVICES = 'devices'
CONF_DISARM_AFTER_TRIGGER = 'disarm_after_trigger'
CONF_DISCOVERY = 'discovery'
CONF_DISPLAY_OPTIONS = 'display_options'
CONF_DOMAIN = 'domain'
CONF_DOMAINS = 'domains'
CONF_EFFECT = 'effect'
CONF_ELEVATION = 'elevation'
CONF_EMAIL = 'email'
CONF_ENTITIES = 'entities'
CONF_ENTITY_ID = 'entity_id'
CONF_ENTITY_NAMESPACE = 'entity_namespace'
CONF_EVENT = 'event'
CONF_EXCLUDE = 'exclude'
CONF_FILE_PATH = 'file_path'
CONF_FILENAME = 'filename'
CONF_FRIENDLY_NAME = 'friendly_name'
CONF_HEADERS = 'headers'
CONF_HOST = 'host'
CONF_HOSTS = 'hosts'
CONF_ICON = 'icon'
CONF_INCLUDE = 'include'
CONF_ID = 'id'
CONF_LATITUDE = 'latitude'
CONF_LONGITUDE = 'longitude'
CONF_MAC = 'mac'
CONF_METHOD = 'method'
CONF_MINIMUM = 'minimum'
CONF_MAXIMUM = 'maximum'
CONF_MONITORED_CONDITIONS = 'monitored_conditions'
CONF_MONITORED_VARIABLES = 'monitored_variables'
CONF_NAME = 'name'
CONF_OFFSET = 'offset'
CONF_OPTIMISTIC = 'optimistic'
CONF_PACKAGES = 'packages'
CONF_PASSWORD = 'password'
CONF_PATH = 'path'
CONF_PAYLOAD = 'payload'
CONF_PAYLOAD_OFF = 'payload_off'
CONF_PAYLOAD_ON = 'payload_on'
CONF_PENDING_TIME = 'pending_time'
CONF_PIN = 'pin'
CONF_PLATFORM = 'platform'
CONF_PORT = 'port'
CONF_PREFIX = 'prefix'
CONF_PROTOCOL = 'protocol'
CONF_PROXY_SSL = 'proxy_ssl'
CONF_QUOTE = 'quote'
CONF_RECIPIENT = 'recipient'
CONF_RESOURCE = 'resource'
CONF_RESOURCES = 'resources'
CONF_RGB = 'rgb'
CONF_SCAN_INTERVAL = 'scan_interval'
CONF_SENDER = 'sender'
CONF_SENSOR_CLASS = 'sensor_class'
CONF_SENSORS = 'sensors'
CONF_SSL = 'ssl'
CONF_STATE = 'state'
CONF_STRUCTURE = 'structure'
CONF_SWITCHES = 'switches'
CONF_TEMPERATURE_UNIT = 'temperature_unit'
CONF_TIME_ZONE = 'time_zone'
CONF_TIMEOUT = 'timeout'
CONF_TOKEN = 'token'
CONF_TRIGGER_TIME = 'trigger_time'
CONF_TYPE = 'type'
CONF_UNIT_OF_MEASUREMENT = 'unit_of_measurement'
CONF_UNIT_SYSTEM = 'unit_system'
CONF_URL = 'url'
CONF_USERNAME = 'username'
CONF_VALUE_TEMPLATE = 'value_template'
CONF_VERIFY_SSL = 'verify_ssl'
CONF_WEEKDAY = 'weekday'
CONF_WHITELIST = 'whitelist'
CONF_WHITE_VALUE = 'white_value'
CONF_XY = 'xy'
CONF_ZONE = 'zone'

# #### EVENTS ####
EVENT_HOMEASSISTANT_START = 'homeassistant_start'
EVENT_HOMEASSISTANT_STOP = 'homeassistant_stop'
EVENT_HOMEASSISTANT_CLOSE = 'homeassistant_close'
EVENT_STATE_CHANGED = 'state_changed'
EVENT_TIME_CHANGED = 'time_changed'
EVENT_CALL_SERVICE = 'call_service'
EVENT_SERVICE_EXECUTED = 'service_executed'
EVENT_PLATFORM_DISCOVERED = 'platform_discovered'
EVENT_COMPONENT_LOADED = 'component_loaded'
EVENT_SERVICE_REGISTERED = 'service_registered'
EVENT_SERVICE_REMOVED = 'service_removed'

# #### STATES ####
STATE_ON = 'on'
STATE_OFF = 'off'
STATE_HOME = 'home'
STATE_NOT_HOME = 'not_home'
STATE_UNKNOWN = 'unknown'
STATE_OPEN = 'open'
STATE_CLOSED = 'closed'
STATE_PLAYING = 'playing'
STATE_PAUSED = 'paused'
STATE_IDLE = 'idle'
STATE_STANDBY = 'standby'
STATE_ALARM_DISARMED = 'disarmed'
STATE_ALARM_ARMED_HOME = 'armed_home'
STATE_ALARM_ARMED_AWAY = 'armed_away'
STATE_ALARM_PENDING = 'pending'
STATE_ALARM_TRIGGERED = 'triggered'
STATE_LOCKED = 'locked'
STATE_UNLOCKED = 'unlocked'
STATE_UNAVAILABLE = 'unavailable'

# #### STATE AND EVENT ATTRIBUTES ####
# Attribution
ATTR_ATTRIBUTION = 'attribution'

# Contains current time for a TIME_CHANGED event
ATTR_NOW = 'now'

# Contains domain, service for a SERVICE_CALL event
ATTR_DOMAIN = 'domain'
ATTR_SERVICE = 'service'
ATTR_SERVICE_DATA = 'service_data'

# Data for a SERVICE_EXECUTED event
ATTR_SERVICE_CALL_ID = 'service_call_id'

# Contains one string or a list of strings, each being an entity id
ATTR_ENTITY_ID = 'entity_id'

# String with a friendly name for the entity
ATTR_FRIENDLY_NAME = 'friendly_name'

# A picture to represent entity
ATTR_ENTITY_PICTURE = 'entity_picture'

# Icon to use in the frontend
ATTR_ICON = 'icon'

# The unit of measurement if applicable
ATTR_UNIT_OF_MEASUREMENT = 'unit_of_measurement'

CONF_UNIT_SYSTEM_METRIC = 'metric'  # type: str
CONF_UNIT_SYSTEM_IMPERIAL = 'imperial'  # type: str

# Temperature attribute
ATTR_TEMPERATURE = 'temperature'
TEMP_CELSIUS = '°C'
TEMP_FAHRENHEIT = '°F'

# Length units
LENGTH_CENTIMETERS = 'cm'  # type: str
LENGTH_METERS = 'm'  # type: str
LENGTH_KILOMETERS = 'km'  # type: str

LENGTH_INCHES = 'in'  # type: str
LENGTH_FEET = 'ft'  # type: str
LENGTH_YARD = 'yd'  # type: str
LENGTH_MILES = 'mi'  # type: str

# Volume units
VOLUME_LITERS = 'L'  # type: str
VOLUME_MILLILITERS = 'mL'  # type: str

VOLUME_GALLONS = 'gal'  # type: str
VOLUME_FLUID_OUNCE = 'fl. oz.'  # type: str

# Mass units
MASS_GRAMS = 'g'  # type: str
MASS_KILOGRAMS = 'kg'  # type: str

MASS_OUNCES = 'oz'  # type: str
MASS_POUNDS = 'lb'  # type: str

# Contains the information that is discovered
ATTR_DISCOVERED = 'discovered'

# Location of the device/sensor
ATTR_LOCATION = 'location'

ATTR_BATTERY_LEVEL = 'battery_level'
ATTR_WAKEUP = 'wake_up_interval'

# For devices which support a code attribute
ATTR_CODE = 'code'
ATTR_CODE_FORMAT = 'code_format'

# For devices which support an armed state
ATTR_ARMED = 'device_armed'

# For devices which support a locked state
ATTR_LOCKED = 'locked'

# For sensors that support 'tripping', eg. motion and door sensors
ATTR_TRIPPED = 'device_tripped'

# For sensors that support 'tripping' this holds the most recent
# time the device was tripped
ATTR_LAST_TRIP_TIME = 'last_tripped_time'

# For all entity's, this hold whether or not it should be hidden
ATTR_HIDDEN = 'hidden'

# Location of the entity
ATTR_LATITUDE = 'latitude'
ATTR_LONGITUDE = 'longitude'

# Accuracy of location in meters
ATTR_GPS_ACCURACY = 'gps_accuracy'

# If state is assumed
ATTR_ASSUMED_STATE = 'assumed_state'
ATTR_STATE = 'state'

ATTR_OPTION = 'option'

# Bitfield of supported component features for the entity
ATTR_SUPPORTED_FEATURES = 'supported_features'

# Class of device within its domain
ATTR_DEVICE_CLASS = 'device_class'

# #### SERVICES ####
SERVICE_HOMEASSISTANT_STOP = 'stop'
SERVICE_HOMEASSISTANT_RESTART = 'restart'

SERVICE_TURN_ON = 'turn_on'
SERVICE_TURN_OFF = 'turn_off'
SERVICE_TOGGLE = 'toggle'
SERVICE_RELOAD = 'reload'

SERVICE_VOLUME_UP = 'volume_up'
SERVICE_VOLUME_DOWN = 'volume_down'
SERVICE_VOLUME_MUTE = 'volume_mute'
SERVICE_VOLUME_SET = 'volume_set'
SERVICE_MEDIA_PLAY_PAUSE = 'media_play_pause'
SERVICE_MEDIA_PLAY = 'media_play'
SERVICE_MEDIA_PAUSE = 'media_pause'
SERVICE_MEDIA_STOP = 'media_stop'
SERVICE_MEDIA_NEXT_TRACK = 'media_next_track'
SERVICE_MEDIA_PREVIOUS_TRACK = 'media_previous_track'
SERVICE_MEDIA_SEEK = 'media_seek'

SERVICE_ALARM_DISARM = 'alarm_disarm'
SERVICE_ALARM_ARM_HOME = 'alarm_arm_home'
SERVICE_ALARM_ARM_AWAY = 'alarm_arm_away'
SERVICE_ALARM_TRIGGER = 'alarm_trigger'

SERVICE_LOCK = 'lock'
SERVICE_UNLOCK = 'unlock'

SERVICE_OPEN = 'open'
SERVICE_CLOSE = 'close'

SERVICE_CLOSE_COVER = 'close_cover'
SERVICE_CLOSE_COVER_TILT = 'close_cover_tilt'
SERVICE_OPEN_COVER = 'open_cover'
SERVICE_OPEN_COVER_TILT = 'open_cover_tilt'
SERVICE_SET_COVER_POSITION = 'set_cover_position'
SERVICE_SET_COVER_TILT_POSITION = 'set_cover_tilt_position'
SERVICE_STOP_COVER = 'stop_cover'
SERVICE_STOP_COVER_TILT = 'stop_cover_tilt'

SERVICE_SELECT_OPTION = 'select_option'

# #### API / REMOTE ####
SERVER_PORT = 8123

URL_ROOT = '/'
URL_API = '/api/'
URL_API_STREAM = '/api/stream'
URL_API_CONFIG = '/api/config'
URL_API_DISCOVERY_INFO = '/api/discovery_info'
URL_API_STATES = '/api/states'
URL_API_STATES_ENTITY = '/api/states/{}'
URL_API_EVENTS = '/api/events'
URL_API_EVENTS_EVENT = '/api/events/{}'
URL_API_SERVICES = '/api/services'
URL_API_SERVICES_SERVICE = '/api/services/{}/{}'
URL_API_COMPONENTS = '/api/components'
URL_API_ERROR_LOG = '/api/error_log'
URL_API_LOG_OUT = '/api/log_out'
URL_API_TEMPLATE = '/api/template'

HTTP_OK = 200
HTTP_CREATED = 201
HTTP_MOVED_PERMANENTLY = 301
HTTP_BAD_REQUEST = 400
HTTP_UNAUTHORIZED = 401
HTTP_NOT_FOUND = 404
HTTP_METHOD_NOT_ALLOWED = 405
HTTP_UNPROCESSABLE_ENTITY = 422
HTTP_INTERNAL_SERVER_ERROR = 500

HTTP_BASIC_AUTHENTICATION = 'basic'
HTTP_DIGEST_AUTHENTICATION = 'digest'

HTTP_HEADER_HA_AUTH = 'X-HA-access'
HTTP_HEADER_ACCEPT_ENCODING = 'Accept-Encoding'
HTTP_HEADER_CONTENT_TYPE = 'Content-type'
HTTP_HEADER_CONTENT_ENCODING = 'Content-Encoding'
HTTP_HEADER_VARY = 'Vary'
HTTP_HEADER_CONTENT_LENGTH = 'Content-Length'
HTTP_HEADER_CACHE_CONTROL = 'Cache-Control'
HTTP_HEADER_EXPIRES = 'Expires'
HTTP_HEADER_ORIGIN = 'Origin'
HTTP_HEADER_X_REQUESTED_WITH = 'X-Requested-With'
HTTP_HEADER_ACCEPT = 'Accept'
HTTP_HEADER_ACCESS_CONTROL_ALLOW_ORIGIN = 'Access-Control-Allow-Origin'
HTTP_HEADER_ACCESS_CONTROL_ALLOW_HEADERS = 'Access-Control-Allow-Headers'

ALLOWED_CORS_HEADERS = [HTTP_HEADER_ORIGIN, HTTP_HEADER_ACCEPT,
                        HTTP_HEADER_X_REQUESTED_WITH, HTTP_HEADER_CONTENT_TYPE,
                        HTTP_HEADER_HA_AUTH]

CONTENT_TYPE_JSON = 'application/json'
CONTENT_TYPE_MULTIPART = 'multipart/x-mixed-replace; boundary={}'
CONTENT_TYPE_TEXT_PLAIN = 'text/plain'

# The exit code to send to request a restart
RESTART_EXIT_CODE = 100

UNIT_NOT_RECOGNIZED_TEMPLATE = '{} is not a recognized {} unit.'  # type: str

LENGTH = 'length'  # type: str
MASS = 'mass'  # type: str
VOLUME = 'volume'  # type: str
TEMPERATURE = 'temperature'  # type: str
SPEED_MS = 'speed_ms'  # type: str
ILLUMINANCE = 'illuminance'  # type: str
