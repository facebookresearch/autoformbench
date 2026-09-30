ARG AGENT_IMAGE=autoformbench-agent:lean4.32.2-mathlib-905b9581

FROM ${AGENT_IMAGE}

USER root
WORKDIR /app

COPY --chown=agent:agent workspace/ /app/

RUN mkdir -p /app/.lake \
    && ln -s /opt/autoformbench/packages /app/.lake/packages \
    && chown -R --no-dereference agent:agent /app \
    && chmod -R u+rwX,go+rX /app

USER agent
ENV HOME=/home/agent

RUN lake build
