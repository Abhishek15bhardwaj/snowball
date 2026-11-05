// Supabase project used for syncing progress. The anon (publishable) key is meant to be public;
// the database only allows the snow_get / snow_put functions, never table reads.
window.SNOW_CONFIG = {
  url: "",
  key: ""
};
