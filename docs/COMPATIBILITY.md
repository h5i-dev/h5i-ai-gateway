# Compatibility with LiteLLM

What h5i-gateway implements from the LiteLLM proxy, what it does
differently, and what it leaves out.

## Configuration

LiteLLM's `config.yaml`:

- `model_list` with `litellm_params` and `model_info`, and `os.environ/`
  secrets.
- `router_settings`: `num_retries`, `allowed_fails`, `cooldown_time`,
  `timeout`, `fallbacks`, `model_group_alias`.
- `general_settings`: `master_key`, `database_url`.
- `environment_variables`.

## Endpoints

- `/v1/chat/completions` (streaming included), `/v1/embeddings`,
  `/v1/models`, and Azure-style `/openai/deployments/{model}/chat/completions`.
- Anthropic's Messages API and OpenAI's Responses API, bridged to chat
  completions for every provider (see below).
- Images and audio (see [Images and audio](#images-and-audio)).
- Virtual keys: `/key/generate|update|delete|block|unblock|info|list|reset_spend`,
  with `models`, `max_budget`, `budget_duration`, `rpm_limit`, `tpm_limit`,
  `max_parallel_requests`, `duration`, `team_id`, `user_role: proxy_admin`.
- Teams: `/team/new|update|delete|block|unblock|info|list`, with shared
  budgets, limits and model lists.
- `/model/info`, `/global/spend`, `/health/liveliness|readiness`, and
  `/spend/logs` (filters `api_key`, `team_id`, `model`, `status`,
  `start_date`, `end_date`, `limit`).
- An admin UI at `/ui` (see [UI.md](UI.md)).
- The `x-litellm-*` response headers; keys in `Authorization`, `x-api-key`,
  `api-key` or `x-goog-api-key`; `mock_response`.

## Guardrails

Configured with the `guardrails:` list (`mode: pre_call|during_call|post_call`,
`default_on`), selected per request with `guardrails` or
`metadata.guardrails`, and reported in the `x-litellm-applied-guardrails`
header. A block is a 400 of type `guardrail_violation` naming the guardrail.

- `litellm_content_filter`: `blocked_words`, and regex and prebuilt
  `patterns` with `BLOCK` or `MASK` (e-mail, phone, credit cards with a Luhn
  check, US SSN, IPv4/IPv6, AWS keys, GitHub/Slack/OpenAI-style tokens,
  generic API keys, URLs).
- `presidio`: analyzer and anonymizer APIs, `pii_entities_config`, score
  thresholds, `output_parse_pii` (streaming included).
- `openai_moderation`.
- `lakera_v2`: `block` or `monitor`.
- `generic_guardrail_api`: `BLOCKED`, `NONE`, `GUARDRAIL_INTERVENED` with
  rewritten texts, `extra_body` per request, `unreachable_fallback`,
  `fail_on_error`.

## Caching

- Configured with `litellm_settings.cache` and `cache_params`:
  `type: local|redis`, `host`/`port`/`password`/`url`, `ttl`, `namespace`,
  `max_size_in_memory`, `mode: default_off`, `supported_call_types`.
- Caches chat completions (including the Messages and Responses APIs, which
  run on the chat path) and embeddings.
- Per-request `cache: {no-cache, no-store, ttl, s-maxage, namespace, use-cache}`.
- A cached chat is replayed as a stream when `stream: true`.
- Headers `x-litellm-cache-key` and `x-litellm-cache-hit`.

## Providers

LiteLLM's price table is vendored.

- OpenAI and OpenAI-compatible: Azure, Groq, DeepSeek, Mistral, Together,
  Fireworks, OpenRouter, xAI, Perplexity, DeepInfra, Cerebras, NVIDIA NIM,
  SambaNova, vLLM, Ollama, LM Studio.
- Anthropic, and Gemini (AI Studio).
- Amazon Bedrock (`bedrock/`): Converse and ConverseStream for every chat
  model, including `bedrock/converse/`, region paths, cross-region inference
  profiles such as `us.anthropic...` and ARNs; Titan and Cohere embeddings.
  Credentials: SigV4 with `aws_access_key_id`/`aws_secret_access_key`/
  `aws_session_token`/`aws_region_name` or the `AWS_*` variables, or Bedrock
  API keys via `api_key`/`AWS_BEARER_TOKEN_BEDROCK`;
  `aws_bedrock_runtime_endpoint`.
- Google Vertex AI (`vertex_ai/`): Gemini, Claude via `rawPredict` /
  `streamRawPredict`, text embeddings. Credentials: service-account or
  authorized-user `vertex_credentials` / `GOOGLE_APPLICATION_CREDENTIALS`
  exchanged for cached OAuth2 tokens, an access token in `api_key`, or the
  GCE metadata server; `vertex_project`, `vertex_location` including
  `global`.

## Differences

Budgets are enforced with reservations, so
concurrent requests cannot overspend (LiteLLM checks spend after the fact);
rate limits use fixed one-minute windows; routing is priority (`order`),
then least busy, then id (LiteLLM's `routing_strategy` setting is accepted
but not used); deployments come from the configuration file (no
`/model/new`); key, team and user ids are numbers; prompt-cache token prices
are not discounted. A cache hit is admitted by the kernel and settled at
zero tokens (so it counts against RPM and needs model access, but costs
nothing). `post_call` guardrails on a stream run once on the accumulated
text when the upstream ends: the text has already been sent, so a block
ends the stream with an error event and `MASK` rewrites are not applied to
streams. `during_call` and `post_call` blocks come after the provider call,
which is charged. Guardrails apply to chat (and so to the APIs built on it)
and `pre_call` to embedding inputs.

## Anthropic Messages API

`POST /v1/messages`, `/anthropic/v1/messages` and
`/v1/messages/count_tokens`, as LiteLLM's `/v1/messages`. The request is
translated to a chat completion, so any provider serves it and keys,
budgets, rate limits, routing, retries, fallbacks and spend work as for
`/v1/chat/completions`. Supported: `system` as a string or text blocks;
text, `image` (base64 or URL), `document` (base64, plain text, file id)
blocks; `tool_use`/`tool_result`; `tools` (custom tools; server tools such
as `web_search_20250305` pass through to Anthropic only); `tool_choice`
including `disable_parallel_tool_use`; `stop_sequences`, `temperature`,
`top_p`, `top_k`, `metadata.user_id`, `thinking` (forwarded to Anthropic
deployments; mapped to `reasoning_effort` for others), `cache_control`
(kept for Anthropic deployments, dropped for others), `stream`. Responses,
SSE events (`message_start`, `ping`, `content_block_start/delta/stop` with
`text_delta`, `thinking_delta`, `input_json_delta`, `message_delta` with
`stop_reason` and usage, `message_stop`, `error`) and errors
(`{"type": "error", "error": {...}}`) are in Anthropic's shape. Keys may be
sent as `x-api-key`. `count_tokens` returns the gateway's prompt estimate
(no tokenizer) and charges nothing. Not supported: `signature_delta` and
thinking signatures in streamed answers, citations, and server tools on
non-Anthropic deployments.

## OpenAI Responses API

`POST /v1/responses`, and `GET` and `DELETE /v1/responses/{id}`, bridged to
chat completions like LiteLLM's responses-to-chat bridge. Supported: `input` as a string or items (messages with
`input_text`/`input_image`/`input_file`/`input_audio` parts, `function_call`,
`function_call_output`; `reasoning` items are dropped), `instructions`,
function `tools`, `tool_choice`, `max_output_tokens`, `temperature`,
`top_p`, `text.format` (`json_schema`, `json_object`), `reasoning.effort`,
`parallel_tool_calls`, `stream` (`response.created`, `response.in_progress`,
`response.output_item.added/done`, `response.content_part.added/done`,
`response.output_text.delta/done`, `response.function_call_arguments.delta/done`,
`response.reasoning_summary_*`, `response.completed`/`response.incomplete`,
`error`/`response.failed`, all with `sequence_number`s), `store` and
`previous_response_id`. Output items are `message` (`output_text`),
`function_call` and `reasoning` (as summary text). **Stored responses are
kept in memory** in the gateway process (lost on restart, not shared between
replicas), at most `H5I_RESPONSES_STORE_SIZE` of them (default 1000, least
recently used evicted), each visible only to the key that created it. Not
supported: hosted tools (web/file search, computer use, code interpreter,
MCP), `background`, `item_reference` inputs, `input_file.file_url`,
`/v1/responses/{id}/input_items`, conversations, and
`/v1/responses/{id}/cancel`.

## Not implemented

The other non-OpenAI-compatible providers; Bedrock
InvokeModel chat (`bedrock/invoke/` is served through Converse), AWS
role/profile/web-identity credentials and the instance-metadata chain, Nova
and TwelveLabs embeddings, media given to Bedrock as `http(s)` URLs (send
base64 or `s3://`); Vertex AI workload-identity federation
(`external_account`), partner models other than Claude, Model Garden
endpoints; `/v1/completions`, files and batches; the other
guardrail integrations (Bedrock, Aporia, Azure, …), content filter
`categories` and `blocked_words_file`, LiteLLM's older
`litellm_settings.guardrails` format, and semantic, S3, disk and
Redis-cluster caches; callbacks other than the spend log webhook, and SSO;
users, organizations and budgets per customer or per model.

## Images and audio

| Endpoint | Providers |
|---|---|
| `POST /v1/images/generations` (`prompt, n, size, quality, style, response_format, background, output_format, user`, other fields passed through) | OpenAI (dall-e-2/3, gpt-image-*), Azure OpenAI, OpenAI-compatible providers that serve the endpoint (xAI, Together, …), Gemini AI Studio (Imagen via `:predict`; `gemini-*-image` via `:generateContent`) |
| `POST /v1/images/edits` (multipart `image`/`image[]`, `mask`, `prompt`, `n`, `size`, …) | OpenAI, Azure OpenAI, OpenAI-compatible |
| `POST /v1/audio/transcriptions`, `/v1/audio/translations` (multipart `file, model, language, prompt, response_format, temperature, timestamp_granularities[]`, …) | OpenAI (whisper-1, gpt-4o-transcribe, …), Azure OpenAI, Groq and other OpenAI-compatible servers; `text`/`srt`/`vtt` pass through with the upstream's content type |
| `POST /v1/audio/speech` (`model, input, voice, response_format, speed, instructions`) | OpenAI, Azure OpenAI, OpenAI-compatible; the audio is streamed back with its content type |

Each is also served without `/v1` and as Azure's
`/openai/deployments/{model}/...`; uploads are limited to 64 MiB;
`mock_response` (request field, form field or `litellm_params`) answers
offline (`n` copies of the given image URL, the given transcript, or a
short silent WAV) and honours LiteLLM's error triggers. A deployment serves
a media endpoint when its mode (`model_info.mode`, else LiteLLM's table,
else implied by its own media prices) matches; a chat deployment is
refused.

**Units and prices.** The kernel charges `prompt_units * input_cost +
completion_units * output_cost`, so a media deployment's prices are per
media unit, taken from LiteLLM's table or the deployment's own
`litellm_params`/`model_info` (`output_cost_per_image`,
`input_cost_per_image`, `input_cost_per_pixel`,
`output_cost_per_image_token`, `input_cost_per_image_token`,
`input_cost_per_second`, `output_cost_per_second`,
`input_cost_per_character`, `input_cost_per_audio_token`,
`input_cost_per_token`, `output_cost_per_token`); the module docs of
`crates/gateway-server/src/media/pricing.rs` give the details.

- *Per-image models* (DALL-E, Imagen): a completion unit is a thousandth
  of the deployment's most expensive size/quality variant
  (`hd/1024-x-1792/dall-e-3`, Azure's per-pixel prices, or a flat
  `output_cost_per_image`); an image costing `p` is `ceil(p / unit)` units.
  Admission reserves `n` images at the dearest variant the request's `size`
  and `quality` allow (every variant for `auto`; DALL-E 3 defaults to
  standard 1024x1024); settlement counts the images returned at the variant
  generated. Rounding overcharges by under 0.1% of the top price per image.
  OpenAI's DALL-E prices, no longer in the vendored table, are built in.
- *Token-priced image models* (gpt-image, Gemini image models): completion
  units are output image tokens, prompt units text tokens. The reported
  usage is charged (input image tokens and output text/thinking tokens
  converted at their price ratios); without usage, the table's per-image
  variant price. The reservation is the prompt's UTF-8 length, 8,000 image
  tokens per uploaded image, and per output image the larger of the
  variant price in tokens and OpenAI's token counts for the size and
  quality (Gemini: 1,400, or 2,600 above 2K, plus 2,048 text tokens).
- *Transcription*: a prompt unit is a second of audio at the per-second
  price (`output_cost_per_second` if set, else `input_cost_per_second`, as
  LiteLLM). The reservation is the upload's duration read from its
  container (WAV, FLAC, MP4/M4A, Ogg, MP3 Xing/VBRI headers; for other MP3s
  the format's lowest bitrate, and for unknown formats 6 kbps, as bounds);
  settlement uses the provider's reported duration (`duration`,
  `usage.seconds`), else the container's, else the last subtitle cue,
  rounded up to whole seconds. Models reporting token usage
  (gpt-4o-transcribe) are charged it, converted to seconds-units, with
  output tokens as completion units.
- *Speech*: a prompt unit is an input character at
  `input_cost_per_character`; the cost is known before the call, so the
  reservation is exact. Token-priced TTS (gpt-4o-mini-tts) is charged its
  estimated input tokens (characters / 4), like LiteLLM.

Media units also count towards TPM limits. A model group should hold one
kind of deployment; a mixed group reserves the largest of each
deployment's own reservation. Not implemented: streamed transcriptions
(`stream: true`), Gemini image edits, Gemini/Vertex speech and
transcription, image variations, and pricing of the audio output of
token-priced TTS models.
