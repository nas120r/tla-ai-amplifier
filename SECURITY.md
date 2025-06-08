# Security Policy

## Supported Versions

We currently support the following versions with security updates:

| Version | Supported          |
| ------- | ------------------ |
| 1.0.x   | :white_check_mark: |

## Reporting a Vulnerability

We take the security of TLA+ AI Amplifier seriously. If you believe you've found a security vulnerability, please follow these steps:

1. **Do not disclose the vulnerability publicly**
2. **Email the details to** (project maintainer email)
3. **Include the following information**:
   - Description of the vulnerability
   - Steps to reproduce
   - Potential impact
   - Any suggested fixes (if available)

## What to Expect

- You'll receive an acknowledgment within 48 hours
- We'll investigate and provide a timeline for a fix
- We'll keep you updated on the progress
- Once the issue is resolved, we'll publish a security advisory

## Security Considerations for TLA+ Projects

When working with TLA+ specifications and related code:

1. **Never embed credentials or sensitive information** in specifications or example code
2. **Be cautious with file paths** in examples and tools
3. **Validate all inputs** when building tools around TLA+ specifications
4. **Keep dependencies updated** to avoid known vulnerabilities

## Best Practices

- Regularly update project dependencies
- Review code for potential security issues
- Follow secure coding guidelines
- Use static analysis tools where applicable

## Vulnerabilities in Dependencies

We use automated tools to scan for vulnerabilities in dependencies and will update them as needed.