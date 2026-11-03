# Security regression tests (`h5i test`)

`tests/*.yaml` replay attacks against a running gateway; CI starts one with
`gateway.yaml` in front of the bench crate's mock upstream and runs
`h5i test --target http://127.0.0.1:4000`. Locally:

```sh
cargo run -p gateway-bench --bin mock-upstream -- --port 9000 &
LITELLM_MASTER_KEY=sk-ci-master cargo run -p gateway-server -- --config .h5i-tests/gateway.yaml --port 4000 &
LITELLM_MASTER_KEY=sk-ci-master h5i test --target http://127.0.0.1:4000
```

## `tests/litellm-*.yaml`: LiteLLM's known vulnerabilities

Each test is a port of a [nuclei-templates](https://github.com/projectdiscovery/nuclei-templates)
template for a LiteLLM proxy vulnerability, kept so the port never acquires
it. A Nuclei matcher detects the vulnerability, so these verdicts are its
negation: a test passes when the attack fails.

`h5i websec import-nuclei` takes a template with no Nuclei variables
directly (`litellm-unauth-model-exposure.yaml`, with its verdict wrapped in `not`).
The others use variables, `flow` blocks, raw requests or out-of-band
(interactsh) matchers, which the importer refuses; they are ported by hand
with concrete values. h5i's `expect` has no response time, so a template's
time-based check (`duration >= 8`) becomes the functional property instead:
the payload is refused and the gateway still answers.
